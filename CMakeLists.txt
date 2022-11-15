project(ValueNumbering)
cmake_minimum_required(VERSION 3.9)

# find LLVM packages
set(LLVM_DIR /Users/ql/Downloads/CS201-F22-Template/LLVM/lib/cmake/llvm)
set(CMAKE_PREFIX_PATH /Users/ql/Downloads/CS201-F22-Template/LLVM/lib/cmake)
find_package(LLVM REQUIRED CONFIG)
add_definitions(${LLVM_DEFINITIONS})
include_directories(${LLVM_INCLUDE_DIRS})

# set C++ compiler standard and flags
set(CMAKE_CXX_STANDARD 14)
SET (CMAKE_CXX_FLAGS "-fno-rtti -fPIC")

# bug fix on MacOSX
SET(CMAKE_MODULE_LINKER_FLAGS "-undefined dynamic_lookup")

add_library(LLVMLivenessAnalysisPass MODULE LivenessAnalysis.cpp)
set_target_properties(LLVMLivenessAnalysisPass PROPERTIES COMPILE_FLAGS "-D__GLIBCXX_USE_CXX11_ABI=0 ")

target_link_libraries(LLVMLivenessAnalysisPass)


