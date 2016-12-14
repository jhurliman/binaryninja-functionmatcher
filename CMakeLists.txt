cmake_minimum_required(VERSION 3.0.0 FATAL_ERROR)

project(functionmatcher)

find_package(Boost 1.56 REQUIRED COMPONENTS graph)

add_library(${PROJECT_NAME} SHARED
	src/functionmatcher.cpp
	src/sqlite/mem/memory.hpp
	src/sqlite/database.cpp
	src/sqlite/database.hpp
	src/sqlite/error.cpp
	src/sqlite/error.hpp
	src/sqlite/field.cpp
	src/sqlite/field.hpp
	src/sqlite/result.cpp
	src/sqlite/result.hpp
	src/sqlite/row.cpp
	src/sqlite/row.hpp
	src/sqlite/sqlite3.c
	src/sqlite/sqlite3.h
	src/sqlite/statement.cpp
	src/sqlite/statement.hpp
	)

source_group(src\\sqlite\\mem FILES
	src/sqlite/mem/memory.hpp
	)

source_group(src\\sqlite FILES
	src/sqlite/database.cpp
	src/sqlite/database.hpp
	src/sqlite/error.cpp
	src/sqlite/error.hpp
	src/sqlite/field.cpp
	src/sqlite/field.hpp
	src/sqlite/result.cpp
	src/sqlite/result.hpp
	src/sqlite/row.cpp
	src/sqlite/row.hpp
	src/sqlite/sqlite3.c
	src/sqlite/sqlite3.h
	src/sqlite/statement.cpp
	src/sqlite/statement.hpp
	)

source_group(src FILES
	src/functionmatcher.cpp
	)

include_directories(${Boost_INCLUDE_DIRS})
include_directories(${CMAKE_CURRENT_SOURCE_DIR}/binaryninja-api)

if(WIN32)
	set(BINJA_DIR "C:\\Program Files\\Vector35\\Binary Ninja"
		CACHE PATH "Binary Ninja installation directory")
	set(BINJA_BIN_DIR "${BINJA_DIR}")
	set(BINJA_PLUGINS_DIR "$ENV{APPDATA}/Binary Ninja/plugins"
		CACHE PATH "Binary Ninja user plugins directory")
elseif(APPLE)
	set(BINJA_DIR "/Applications/Binary Ninja.app"
		CACHE PATH "Binary Ninja installation directory")
	set(BINJA_BIN_DIR "${BINJA_DIR}/Contents/MacOS")
	set(BINJA_PLUGINS_DIR "$ENV{HOME}/Library/Application Support/Binary Ninja/plugins"
		CACHE PATH "Binary Ninja user plugins directory")
else()
	set(BINJA_DIR "$ENV{HOME}/binaryninja"
		CACHE PATH "Binary Ninja installation directory")
	set(BINJA_BIN_DIR "${BINJA_DIR}")
	set(BINJA_PLUGINS_DIR "$ENV{HOME}/.binaryninja/plugins"
		CACHE PATH "Binary Ninja user plugins directory")
endif()

add_subdirectory(binaryninja-api ${CMAKE_CURRENT_SOURCE_DIR}/bin)

find_library(BINJA_CORE_LIBRARY binaryninjacore
	HINTS ${BINJA_BIN_DIR})

target_link_libraries(${PROJECT_NAME}
	${Boost_LIBRARIES}
	${BINJA_CORE_LIBRARY}
	binaryninjaapi
	)

set_target_properties(${PROJECT_NAME} PROPERTIES
	CXX_STANDARD 11
	LIBRARY_OUTPUT_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/bin
	)

set_source_files_properties(src/sqlite/sqlite3.c PROPERTIES
	LANGUAGE C
	)

install(TARGETS ${PROJECT_NAME} DESTINATION ${BINJA_PLUGINS_DIR})
