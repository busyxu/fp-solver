#----------------------------------------------------------------
# Generated CMake target import file for configuration "Debug".
#----------------------------------------------------------------

# Commands may need to know the format version.
set(CMAKE_IMPORT_FILE_VERSION 1)

# Import target "NLopt::nlopt" for configuration "Debug"
set_property(TARGET NLopt::nlopt APPEND PROPERTY IMPORTED_CONFIGURATIONS DEBUG)
set_target_properties(NLopt::nlopt PROPERTIES
  IMPORTED_LOCATION_DEBUG "${_IMPORT_PREFIX}/lib/libnlopt.so.0.11.1"
  IMPORTED_SONAME_DEBUG "libnlopt.so.0"
  )

list(APPEND _IMPORT_CHECK_TARGETS NLopt::nlopt )
list(APPEND _IMPORT_CHECK_FILES_FOR_NLopt::nlopt "${_IMPORT_PREFIX}/lib/libnlopt.so.0.11.1" )

# Commands beyond this point should not need to know the version.
set(CMAKE_IMPORT_FILE_VERSION)
