cmake_minimum_required(VERSION 3.20)

set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

set(CMAKE_FIND_PACKAGE_SORT_ORDER NATURAL)
set(CMAKE_FIND_PACKAGE_SORT_DIRECTION DEC)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

project(llvm-ub-aware-interpreter)

find_package(LLVM REQUIRED CONFIG)
message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")
include(AddLLVM)

include_directories(${LLVM_INCLUDE_DIRS})
set(LLVM_LINK_COMPONENTS core support irreader irprinter targetparser analysis transformutils)
add_compile_options("-Wall")
if (LLUBI_ENABLE_SANITIZER)
add_compile_options("-ggdb")
add_compile_options("-fsanitize=address,undefined")
add_link_options("-fsanitize=address,undefined")
endif(LLUBI_ENABLE_SANITIZER)

add_llvm_library(ubi PARTIAL_SOURCES_INTENDED ubi.cpp)
add_llvm_executable(llubi PARTIAL_SOURCES_INTENDED llubi.cpp)
target_link_libraries(llubi PRIVATE ubi)
add_llvm_executable(emireduce PARTIAL_SOURCES_INTENDED emireduce.cpp)
target_link_libraries(emireduce PRIVATE ubi)
