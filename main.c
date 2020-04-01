/*
 * Copyright 2011 Leiden University. All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 
 *    1. Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 * 
 *    2. Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 * 
 * THIS SOFTWARE IS PROVIDED BY LEIDEN UNIVERSITY ''AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL LEIDEN UNIVERSITY OR
 * CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
 * EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
 * PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * 
 * The views and conclusions contained in the software and documentation
 * are those of the authors and should not be interpreted as
 * representing official policies, either expressed or implied, of
 * Leiden University.
 */ 

#include <string.h>

#include <isl/arg.h>
#include <isl/ctx.h>
#include <isl/flow.h>
#include <isl/options.h>

#include "options.h"
#include "scop.h"
#include "scop_yaml.h"

struct options {
	struct isl_options	*isl;
	struct pet_options	*pet;
	char			*input;
};

ISL_ARGS_START(struct options, options_args)
ISL_ARG_CHILD(struct options, isl, "isl", &isl_options_args, "isl options")
ISL_ARG_CHILD(struct options, pet, NULL, &pet_options_args, "pet options")
ISL_ARG_ARG(struct options, input, "input", NULL)
ISL_ARGS_END

ISL_ARG_DEF(options, struct options, options_args)

void print_isl_union_map(struct isl_ctx* ctx, struct isl_union_map *union_map) {
  isl_printer *p = isl_printer_to_str(ctx);
  p = isl_printer_print_union_map(p, union_map);
  char *str = isl_printer_get_str(p);
  isl_printer_free(p);
  for (int i = 0; i < strlen(str); ++i)  putchar(str[i]);
  putchar('\n');
  free(str);
}
  
void print_isl_schedule(struct isl_schedule *schedule) {
  isl_printer *p = isl_printer_to_str(isl_schedule_get_ctx(schedule));
  p = isl_printer_print_schedule(p, schedule);
  char *str = isl_printer_get_str(p);
  isl_printer_free(p);
  for (int i = 0; i < strlen(str); ++i)  putchar(str[i]);
  putchar('\n');
  free(str);
}

static int is_not_kill(struct pet_stmt *stmt)
{
  return !pet_stmt_is_kill(stmt);
}

static __isl_give isl_union_set *collect_domains(struct pet_scop *scop,
      int (*pred)(struct pet_stmt *stmt))
{
  int i;
  isl_set *domain_i;
  isl_union_set *domain;

  if (!scop)
    return NULL;

  domain = isl_union_set_empty(isl_set_get_space(scop->context));

  for (i = 0; i < scop->n_stmt; ++i) {
    struct pet_stmt *stmt = scop->stmts[i];

    if (!pred(stmt))
      continue;

    if (stmt->n_arg > 0)
      isl_die(isl_union_set_get_ctx(domain), isl_error_unsupported,
          "data dependent conditions not supported",
          return isl_union_set_free(domain));

    domain_i = isl_set_copy(scop->stmts[i]->domain);
    domain = isl_union_set_add_set(domain, domain_i);
  }

  return domain;
}

static __isl_give isl_union_set *collect_non_kill_domains(struct pet_scop *scop)
{
  return collect_domains(scop, &is_not_kill);
}
  
void compute_flow_dep(struct pet_scop *scop, isl_union_map **dep_flow,
    isl_union_map **dep_false, isl_ctx **flow_ctx) {
  // compute the potential flow dependences
  // line 685 @ppcg.c
  isl_union_access_info *access;
  isl_union_flow *flow;
  isl_union_map *kills, *must_writes;

  access = isl_union_access_info_from_sink(
      isl_union_map_copy(pet_scop_get_may_reads(scop)));
  kills = isl_union_map_copy(pet_scop_get_must_kills(scop));
  must_writes = isl_union_map_copy(pet_scop_get_must_writes(scop));
  kills = isl_union_map_union(kills, must_writes);
  access = isl_union_access_info_set_kill(access, kills);
  access = isl_union_access_info_set_may_source(access,
      isl_union_map_copy(pet_scop_get_may_writes(scop)));
  access = isl_union_access_info_set_schedule(access,
      isl_schedule_copy(scop->schedule));
  flow = isl_union_access_info_compute_flow(access);
  
  isl_ctx *ctx = isl_union_flow_get_ctx(flow);
  *flow_ctx = ctx;
  *dep_flow = isl_union_flow_get_may_dependence(flow);
  // print_isl_union_map(ctx, dep_flow);
  isl_union_flow_free(flow);

  // line 736 @ppcg.c
  isl_union_map *may_source = isl_union_map_union(isl_union_map_copy(
        pet_scop_get_may_writes(scop)), isl_union_map_copy(
        pet_scop_get_may_reads(scop)));
  access = isl_union_access_info_from_sink(isl_union_map_copy(
        pet_scop_get_may_writes(scop)));
  access = isl_union_access_info_set_kill(access, isl_union_map_copy(
        pet_scop_get_must_writes(scop)));
  access = isl_union_access_info_set_may_source(access, may_source);
  access = isl_union_access_info_set_schedule(access,
                      isl_schedule_copy(scop->schedule));
  flow = isl_union_access_info_compute_flow(access);

  *dep_false = isl_union_flow_get_may_dependence(flow);
  *dep_false = isl_union_map_coalesce(*dep_false);
  isl_union_flow_free(flow);
}

// line 4378 construct_schedule_constraints @gpu.c
void compute_schedule(struct pet_scop *scop, isl_union_map *dep_flow,
    isl_union_map *dep_false, isl_ctx* flow_ctx) {
  isl_union_set *domain;
  isl_union_map *dep_raw, *dep;
  isl_union_map *validity, *proximity, *coincidence;
  isl_schedule_constraints *sc;

  domain = isl_union_set_copy(collect_non_kill_domains(scop));
  sc = isl_schedule_constraints_on_domain(domain);
  sc = isl_schedule_constraints_set_context(sc, isl_set_copy(scop->context));

  dep_raw = isl_union_map_copy(dep_flow);
  dep = isl_union_map_copy(dep_false);
  dep = isl_union_map_union(dep, dep_raw);
  dep = isl_union_map_coalesce(dep);
  proximity = isl_union_map_copy(dep);
  coincidence = isl_union_map_copy(dep);
  validity = dep;

  sc = isl_schedule_constraints_set_validity(sc, validity);
  sc = isl_schedule_constraints_set_coincidence(sc, coincidence);
  sc = isl_schedule_constraints_set_proximity(sc, proximity);

  isl_schedule *schedule = isl_schedule_constraints_compute_schedule(sc);
  print_isl_schedule(schedule);
}

int main(int argc, char *argv[])
{
	isl_ctx *ctx;
	struct pet_scop *scop;
	struct options *options;

	options = options_new_with_defaults();
	ctx = isl_ctx_alloc_with_options(&options_args, options);
	argc = options_parse(options, argc, argv, ISL_ARG_ALL);

	scop = pet_scop_extract_from_C_source(ctx, options->input, NULL);
  struct isl_union_map *dep_flow;
  struct isl_union_map *dep_false;
  struct isl_ctx *flow_ctx;
  compute_flow_dep(scop, &dep_flow, &dep_false, &flow_ctx);
  compute_schedule(scop, dep_flow, dep_false, flow_ctx);

	// if (scop)
	// 	pet_scop_emit(stdout, scop);

	pet_scop_free(scop);

	isl_ctx_free(ctx);
	return 0;
}
