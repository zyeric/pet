cmake_minimum_required(VERSION 3.0)

project (pet_parser C)

set(TARGET_NAME pet_parser)

include_directories(./pet_include/libyaml/include)
include_directories(./include)

link_directories(./pet_lib)

set(SRCS main.c emit.c)

add_executable(${TARGET_NAME} ${SRCS})
target_link_libraries(${TARGET_NAME} -lpet -lisl -lyaml)
