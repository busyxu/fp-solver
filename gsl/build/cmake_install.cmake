# Install script for directory: /home/aaa/gsl

# Set the install prefix
if(NOT DEFINED CMAKE_INSTALL_PREFIX)
  set(CMAKE_INSTALL_PREFIX "/usr/local")
endif()
string(REGEX REPLACE "/$" "" CMAKE_INSTALL_PREFIX "${CMAKE_INSTALL_PREFIX}")

# Set the install configuration name.
if(NOT DEFINED CMAKE_INSTALL_CONFIG_NAME)
  if(BUILD_TYPE)
    string(REGEX REPLACE "^[^A-Za-z0-9_]+" ""
           CMAKE_INSTALL_CONFIG_NAME "${BUILD_TYPE}")
  else()
    set(CMAKE_INSTALL_CONFIG_NAME "Debug")
  endif()
  message(STATUS "Install configuration: \"${CMAKE_INSTALL_CONFIG_NAME}\"")
endif()

# Set the component getting installed.
if(NOT CMAKE_INSTALL_COMPONENT)
  if(COMPONENT)
    message(STATUS "Install component: \"${COMPONENT}\"")
    set(CMAKE_INSTALL_COMPONENT "${COMPONENT}")
  else()
    set(CMAKE_INSTALL_COMPONENT)
  endif()
endif()

# Install shared libraries without execute permission?
if(NOT DEFINED CMAKE_INSTALL_SO_NO_EXE)
  set(CMAKE_INSTALL_SO_NO_EXE "1")
endif()

# Is this installation the result of a crosscompile?
if(NOT DEFINED CMAKE_CROSSCOMPILING)
  set(CMAKE_CROSSCOMPILING "FALSE")
endif()

# Set default install directory permissions.
if(NOT DEFINED CMAKE_OBJDUMP)
  set(CMAKE_OBJDUMP "/usr/bin/objdump")
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "gsl" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib" TYPE STATIC_LIBRARY FILES "/home/aaa/gsl/build/libgsl.a")
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "gsl" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib" TYPE STATIC_LIBRARY FILES "/home/aaa/gsl/build/libgslcblas.a")
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "gsl" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/include/gsl" TYPE FILE FILES
    "/home/aaa/gsl/gsl_inline.h"
    "/home/aaa/gsl/gsl_machine.h"
    "/home/aaa/gsl/gsl_math.h"
    "/home/aaa/gsl/gsl_minmax.h"
    "/home/aaa/gsl/gsl_mode.h"
    "/home/aaa/gsl/gsl_nan.h"
    "/home/aaa/gsl/gsl_pow_int.h"
    "/home/aaa/gsl/gsl_precision.h"
    "/home/aaa/gsl/gsl_types.h"
    "/home/aaa/gsl/gsl_version.h"
    "/home/aaa/gsl/blas/gsl_blas.h"
    "/home/aaa/gsl/blas/gsl_blas_types.h"
    "/home/aaa/gsl/block/gsl_block.h"
    "/home/aaa/gsl/block/gsl_block_char.h"
    "/home/aaa/gsl/block/gsl_block_complex_double.h"
    "/home/aaa/gsl/block/gsl_block_complex_float.h"
    "/home/aaa/gsl/block/gsl_block_complex_long_double.h"
    "/home/aaa/gsl/block/gsl_block_double.h"
    "/home/aaa/gsl/block/gsl_block_float.h"
    "/home/aaa/gsl/block/gsl_block_int.h"
    "/home/aaa/gsl/block/gsl_block_long.h"
    "/home/aaa/gsl/block/gsl_block_long_double.h"
    "/home/aaa/gsl/block/gsl_block_short.h"
    "/home/aaa/gsl/block/gsl_block_uchar.h"
    "/home/aaa/gsl/block/gsl_block_uint.h"
    "/home/aaa/gsl/block/gsl_block_ulong.h"
    "/home/aaa/gsl/block/gsl_block_ushort.h"
    "/home/aaa/gsl/block/gsl_check_range.h"
    "/home/aaa/gsl/bspline/gsl_bspline.h"
    "/home/aaa/gsl/bst/gsl_bst.h"
    "/home/aaa/gsl/bst/gsl_bst_avl.h"
    "/home/aaa/gsl/bst/gsl_bst_rb.h"
    "/home/aaa/gsl/bst/gsl_bst_types.h"
    "/home/aaa/gsl/cblas/gsl_cblas.h"
    "/home/aaa/gsl/cdf/gsl_cdf.h"
    "/home/aaa/gsl/cheb/gsl_chebyshev.h"
    "/home/aaa/gsl/combination/gsl_combination.h"
    "/home/aaa/gsl/complex/gsl_complex.h"
    "/home/aaa/gsl/complex/gsl_complex_math.h"
    "/home/aaa/gsl/const/gsl_const.h"
    "/home/aaa/gsl/const/gsl_const_cgs.h"
    "/home/aaa/gsl/const/gsl_const_cgsm.h"
    "/home/aaa/gsl/const/gsl_const_mks.h"
    "/home/aaa/gsl/const/gsl_const_mksa.h"
    "/home/aaa/gsl/const/gsl_const_num.h"
    "/home/aaa/gsl/deriv/gsl_deriv.h"
    "/home/aaa/gsl/dht/gsl_dht.h"
    "/home/aaa/gsl/diff/gsl_diff.h"
    "/home/aaa/gsl/eigen/gsl_eigen.h"
    "/home/aaa/gsl/err/gsl_errno.h"
    "/home/aaa/gsl/err/gsl_message.h"
    "/home/aaa/gsl/fft/gsl_dft_complex.h"
    "/home/aaa/gsl/fft/gsl_dft_complex_float.h"
    "/home/aaa/gsl/fft/gsl_fft.h"
    "/home/aaa/gsl/fft/gsl_fft_complex.h"
    "/home/aaa/gsl/fft/gsl_fft_complex_float.h"
    "/home/aaa/gsl/fft/gsl_fft_halfcomplex.h"
    "/home/aaa/gsl/fft/gsl_fft_halfcomplex_float.h"
    "/home/aaa/gsl/fft/gsl_fft_real.h"
    "/home/aaa/gsl/fft/gsl_fft_real_float.h"
    "/home/aaa/gsl/filter/gsl_filter.h"
    "/home/aaa/gsl/fit/gsl_fit.h"
    "/home/aaa/gsl/histogram/gsl_histogram.h"
    "/home/aaa/gsl/histogram/gsl_histogram2d.h"
    "/home/aaa/gsl/ieee-utils/gsl_ieee_utils.h"
    "/home/aaa/gsl/integration/gsl_integration.h"
    "/home/aaa/gsl/interpolation/gsl_interp.h"
    "/home/aaa/gsl/interpolation/gsl_interp2d.h"
    "/home/aaa/gsl/interpolation/gsl_spline.h"
    "/home/aaa/gsl/interpolation/gsl_spline2d.h"
    "/home/aaa/gsl/linalg/gsl_linalg.h"
    "/home/aaa/gsl/matrix/gsl_matrix.h"
    "/home/aaa/gsl/matrix/gsl_matrix_char.h"
    "/home/aaa/gsl/matrix/gsl_matrix_complex_double.h"
    "/home/aaa/gsl/matrix/gsl_matrix_complex_float.h"
    "/home/aaa/gsl/matrix/gsl_matrix_complex_long_double.h"
    "/home/aaa/gsl/matrix/gsl_matrix_double.h"
    "/home/aaa/gsl/matrix/gsl_matrix_float.h"
    "/home/aaa/gsl/matrix/gsl_matrix_int.h"
    "/home/aaa/gsl/matrix/gsl_matrix_long.h"
    "/home/aaa/gsl/matrix/gsl_matrix_long_double.h"
    "/home/aaa/gsl/matrix/gsl_matrix_short.h"
    "/home/aaa/gsl/matrix/gsl_matrix_uchar.h"
    "/home/aaa/gsl/matrix/gsl_matrix_uint.h"
    "/home/aaa/gsl/matrix/gsl_matrix_ulong.h"
    "/home/aaa/gsl/matrix/gsl_matrix_ushort.h"
    "/home/aaa/gsl/min/gsl_min.h"
    "/home/aaa/gsl/monte/gsl_monte.h"
    "/home/aaa/gsl/monte/gsl_monte_miser.h"
    "/home/aaa/gsl/monte/gsl_monte_plain.h"
    "/home/aaa/gsl/monte/gsl_monte_vegas.h"
    "/home/aaa/gsl/movstat/gsl_movstat.h"
    "/home/aaa/gsl/multifit/gsl_multifit.h"
    "/home/aaa/gsl/multifit/gsl_multifit_nlin.h"
    "/home/aaa/gsl/multifit_nlinear/gsl_multifit_nlinear.h"
    "/home/aaa/gsl/multilarge/gsl_multilarge.h"
    "/home/aaa/gsl/multilarge_nlinear/gsl_multilarge_nlinear.h"
    "/home/aaa/gsl/multimin/gsl_multimin.h"
    "/home/aaa/gsl/multiroots/gsl_multiroots.h"
    "/home/aaa/gsl/multiset/gsl_multiset.h"
    "/home/aaa/gsl/ntuple/gsl_ntuple.h"
    "/home/aaa/gsl/ode-initval/gsl_odeiv.h"
    "/home/aaa/gsl/ode-initval2/gsl_odeiv2.h"
    "/home/aaa/gsl/permutation/gsl_permutation.h"
    "/home/aaa/gsl/permutation/gsl_permute.h"
    "/home/aaa/gsl/permutation/gsl_permute_char.h"
    "/home/aaa/gsl/permutation/gsl_permute_complex_double.h"
    "/home/aaa/gsl/permutation/gsl_permute_complex_float.h"
    "/home/aaa/gsl/permutation/gsl_permute_complex_long_double.h"
    "/home/aaa/gsl/permutation/gsl_permute_double.h"
    "/home/aaa/gsl/permutation/gsl_permute_float.h"
    "/home/aaa/gsl/permutation/gsl_permute_int.h"
    "/home/aaa/gsl/permutation/gsl_permute_long.h"
    "/home/aaa/gsl/permutation/gsl_permute_long_double.h"
    "/home/aaa/gsl/permutation/gsl_permute_matrix.h"
    "/home/aaa/gsl/permutation/gsl_permute_matrix_char.h"
    "/home/aaa/gsl/permutation/gsl_permute_matrix_complex_double.h"
    "/home/aaa/gsl/permutation/gsl_permute_matrix_complex_float.h"
    "/home/aaa/gsl/permutation/gsl_permute_matrix_complex_long_double.h"
    "/home/aaa/gsl/permutation/gsl_permute_matrix_double.h"
    "/home/aaa/gsl/permutation/gsl_permute_matrix_float.h"
    "/home/aaa/gsl/permutation/gsl_permute_matrix_int.h"
    "/home/aaa/gsl/permutation/gsl_permute_matrix_long.h"
    "/home/aaa/gsl/permutation/gsl_permute_matrix_long_double.h"
    "/home/aaa/gsl/permutation/gsl_permute_matrix_short.h"
    "/home/aaa/gsl/permutation/gsl_permute_matrix_uchar.h"
    "/home/aaa/gsl/permutation/gsl_permute_matrix_uint.h"
    "/home/aaa/gsl/permutation/gsl_permute_matrix_ulong.h"
    "/home/aaa/gsl/permutation/gsl_permute_matrix_ushort.h"
    "/home/aaa/gsl/permutation/gsl_permute_short.h"
    "/home/aaa/gsl/permutation/gsl_permute_uchar.h"
    "/home/aaa/gsl/permutation/gsl_permute_uint.h"
    "/home/aaa/gsl/permutation/gsl_permute_ulong.h"
    "/home/aaa/gsl/permutation/gsl_permute_ushort.h"
    "/home/aaa/gsl/permutation/gsl_permute_vector.h"
    "/home/aaa/gsl/permutation/gsl_permute_vector_char.h"
    "/home/aaa/gsl/permutation/gsl_permute_vector_complex_double.h"
    "/home/aaa/gsl/permutation/gsl_permute_vector_complex_float.h"
    "/home/aaa/gsl/permutation/gsl_permute_vector_complex_long_double.h"
    "/home/aaa/gsl/permutation/gsl_permute_vector_double.h"
    "/home/aaa/gsl/permutation/gsl_permute_vector_float.h"
    "/home/aaa/gsl/permutation/gsl_permute_vector_int.h"
    "/home/aaa/gsl/permutation/gsl_permute_vector_long.h"
    "/home/aaa/gsl/permutation/gsl_permute_vector_long_double.h"
    "/home/aaa/gsl/permutation/gsl_permute_vector_short.h"
    "/home/aaa/gsl/permutation/gsl_permute_vector_uchar.h"
    "/home/aaa/gsl/permutation/gsl_permute_vector_uint.h"
    "/home/aaa/gsl/permutation/gsl_permute_vector_ulong.h"
    "/home/aaa/gsl/permutation/gsl_permute_vector_ushort.h"
    "/home/aaa/gsl/poly/gsl_poly.h"
    "/home/aaa/gsl/qrng/gsl_qrng.h"
    "/home/aaa/gsl/randist/gsl_randist.h"
    "/home/aaa/gsl/rng/gsl_rng.h"
    "/home/aaa/gsl/roots/gsl_roots.h"
    "/home/aaa/gsl/rstat/gsl_rstat.h"
    "/home/aaa/gsl/siman/gsl_siman.h"
    "/home/aaa/gsl/sort/gsl_heapsort.h"
    "/home/aaa/gsl/sort/gsl_sort.h"
    "/home/aaa/gsl/sort/gsl_sort_char.h"
    "/home/aaa/gsl/sort/gsl_sort_double.h"
    "/home/aaa/gsl/sort/gsl_sort_float.h"
    "/home/aaa/gsl/sort/gsl_sort_int.h"
    "/home/aaa/gsl/sort/gsl_sort_long.h"
    "/home/aaa/gsl/sort/gsl_sort_long_double.h"
    "/home/aaa/gsl/sort/gsl_sort_short.h"
    "/home/aaa/gsl/sort/gsl_sort_uchar.h"
    "/home/aaa/gsl/sort/gsl_sort_uint.h"
    "/home/aaa/gsl/sort/gsl_sort_ulong.h"
    "/home/aaa/gsl/sort/gsl_sort_ushort.h"
    "/home/aaa/gsl/sort/gsl_sort_vector.h"
    "/home/aaa/gsl/sort/gsl_sort_vector_char.h"
    "/home/aaa/gsl/sort/gsl_sort_vector_double.h"
    "/home/aaa/gsl/sort/gsl_sort_vector_float.h"
    "/home/aaa/gsl/sort/gsl_sort_vector_int.h"
    "/home/aaa/gsl/sort/gsl_sort_vector_long.h"
    "/home/aaa/gsl/sort/gsl_sort_vector_long_double.h"
    "/home/aaa/gsl/sort/gsl_sort_vector_short.h"
    "/home/aaa/gsl/sort/gsl_sort_vector_uchar.h"
    "/home/aaa/gsl/sort/gsl_sort_vector_uint.h"
    "/home/aaa/gsl/sort/gsl_sort_vector_ulong.h"
    "/home/aaa/gsl/sort/gsl_sort_vector_ushort.h"
    "/home/aaa/gsl/spblas/gsl_spblas.h"
    "/home/aaa/gsl/specfunc/gsl_sf.h"
    "/home/aaa/gsl/specfunc/gsl_sf_airy.h"
    "/home/aaa/gsl/specfunc/gsl_sf_bessel.h"
    "/home/aaa/gsl/specfunc/gsl_sf_clausen.h"
    "/home/aaa/gsl/specfunc/gsl_sf_coulomb.h"
    "/home/aaa/gsl/specfunc/gsl_sf_coupling.h"
    "/home/aaa/gsl/specfunc/gsl_sf_dawson.h"
    "/home/aaa/gsl/specfunc/gsl_sf_debye.h"
    "/home/aaa/gsl/specfunc/gsl_sf_dilog.h"
    "/home/aaa/gsl/specfunc/gsl_sf_elementary.h"
    "/home/aaa/gsl/specfunc/gsl_sf_ellint.h"
    "/home/aaa/gsl/specfunc/gsl_sf_elljac.h"
    "/home/aaa/gsl/specfunc/gsl_sf_erf.h"
    "/home/aaa/gsl/specfunc/gsl_sf_exp.h"
    "/home/aaa/gsl/specfunc/gsl_sf_expint.h"
    "/home/aaa/gsl/specfunc/gsl_sf_fermi_dirac.h"
    "/home/aaa/gsl/specfunc/gsl_sf_gamma.h"
    "/home/aaa/gsl/specfunc/gsl_sf_gegenbauer.h"
    "/home/aaa/gsl/specfunc/gsl_sf_hermite.h"
    "/home/aaa/gsl/specfunc/gsl_sf_hyperg.h"
    "/home/aaa/gsl/specfunc/gsl_sf_laguerre.h"
    "/home/aaa/gsl/specfunc/gsl_sf_lambert.h"
    "/home/aaa/gsl/specfunc/gsl_sf_legendre.h"
    "/home/aaa/gsl/specfunc/gsl_sf_log.h"
    "/home/aaa/gsl/specfunc/gsl_sf_mathieu.h"
    "/home/aaa/gsl/specfunc/gsl_sf_pow_int.h"
    "/home/aaa/gsl/specfunc/gsl_sf_psi.h"
    "/home/aaa/gsl/specfunc/gsl_sf_result.h"
    "/home/aaa/gsl/specfunc/gsl_sf_sincos_pi.h"
    "/home/aaa/gsl/specfunc/gsl_sf_synchrotron.h"
    "/home/aaa/gsl/specfunc/gsl_sf_transport.h"
    "/home/aaa/gsl/specfunc/gsl_sf_trig.h"
    "/home/aaa/gsl/specfunc/gsl_sf_zeta.h"
    "/home/aaa/gsl/specfunc/gsl_specfunc.h"
    "/home/aaa/gsl/splinalg/gsl_splinalg.h"
    "/home/aaa/gsl/spmatrix/gsl_spmatrix.h"
    "/home/aaa/gsl/spmatrix/gsl_spmatrix_char.h"
    "/home/aaa/gsl/spmatrix/gsl_spmatrix_complex_double.h"
    "/home/aaa/gsl/spmatrix/gsl_spmatrix_complex_float.h"
    "/home/aaa/gsl/spmatrix/gsl_spmatrix_complex_long_double.h"
    "/home/aaa/gsl/spmatrix/gsl_spmatrix_double.h"
    "/home/aaa/gsl/spmatrix/gsl_spmatrix_float.h"
    "/home/aaa/gsl/spmatrix/gsl_spmatrix_int.h"
    "/home/aaa/gsl/spmatrix/gsl_spmatrix_long.h"
    "/home/aaa/gsl/spmatrix/gsl_spmatrix_long_double.h"
    "/home/aaa/gsl/spmatrix/gsl_spmatrix_short.h"
    "/home/aaa/gsl/spmatrix/gsl_spmatrix_uchar.h"
    "/home/aaa/gsl/spmatrix/gsl_spmatrix_uint.h"
    "/home/aaa/gsl/spmatrix/gsl_spmatrix_ulong.h"
    "/home/aaa/gsl/spmatrix/gsl_spmatrix_ushort.h"
    "/home/aaa/gsl/statistics/gsl_statistics.h"
    "/home/aaa/gsl/statistics/gsl_statistics_char.h"
    "/home/aaa/gsl/statistics/gsl_statistics_double.h"
    "/home/aaa/gsl/statistics/gsl_statistics_float.h"
    "/home/aaa/gsl/statistics/gsl_statistics_int.h"
    "/home/aaa/gsl/statistics/gsl_statistics_long.h"
    "/home/aaa/gsl/statistics/gsl_statistics_long_double.h"
    "/home/aaa/gsl/statistics/gsl_statistics_short.h"
    "/home/aaa/gsl/statistics/gsl_statistics_uchar.h"
    "/home/aaa/gsl/statistics/gsl_statistics_uint.h"
    "/home/aaa/gsl/statistics/gsl_statistics_ulong.h"
    "/home/aaa/gsl/statistics/gsl_statistics_ushort.h"
    "/home/aaa/gsl/sum/gsl_sum.h"
    "/home/aaa/gsl/sys/gsl_sys.h"
    "/home/aaa/gsl/test/gsl_test.h"
    "/home/aaa/gsl/vector/gsl_vector.h"
    "/home/aaa/gsl/vector/gsl_vector_char.h"
    "/home/aaa/gsl/vector/gsl_vector_complex.h"
    "/home/aaa/gsl/vector/gsl_vector_complex_double.h"
    "/home/aaa/gsl/vector/gsl_vector_complex_float.h"
    "/home/aaa/gsl/vector/gsl_vector_complex_long_double.h"
    "/home/aaa/gsl/vector/gsl_vector_double.h"
    "/home/aaa/gsl/vector/gsl_vector_float.h"
    "/home/aaa/gsl/vector/gsl_vector_int.h"
    "/home/aaa/gsl/vector/gsl_vector_long.h"
    "/home/aaa/gsl/vector/gsl_vector_long_double.h"
    "/home/aaa/gsl/vector/gsl_vector_short.h"
    "/home/aaa/gsl/vector/gsl_vector_uchar.h"
    "/home/aaa/gsl/vector/gsl_vector_uint.h"
    "/home/aaa/gsl/vector/gsl_vector_ulong.h"
    "/home/aaa/gsl/vector/gsl_vector_ushort.h"
    "/home/aaa/gsl/wavelet/gsl_wavelet.h"
    "/home/aaa/gsl/wavelet/gsl_wavelet2d.h"
    )
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "gsl" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/pkgconfig" TYPE FILE FILES "/home/aaa/gsl/build/gsl.pc")
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "gsl" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/bin" TYPE PROGRAM FILES "/home/aaa/gsl/build/gsl-config")
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "gsl" OR NOT CMAKE_INSTALL_COMPONENT)
  if(EXISTS "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/cmake/gsl-2.7/gsl-targets.cmake")
    file(DIFFERENT _cmake_export_file_changed FILES
         "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/cmake/gsl-2.7/gsl-targets.cmake"
         "/home/aaa/gsl/build/CMakeFiles/Export/be3280bb442f4242bb46ea3e6d171e46/gsl-targets.cmake")
    if(_cmake_export_file_changed)
      file(GLOB _cmake_old_config_files "$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/cmake/gsl-2.7/gsl-targets-*.cmake")
      if(_cmake_old_config_files)
        string(REPLACE ";" ", " _cmake_old_config_files_text "${_cmake_old_config_files}")
        message(STATUS "Old export file \"$ENV{DESTDIR}${CMAKE_INSTALL_PREFIX}/lib/cmake/gsl-2.7/gsl-targets.cmake\" will be replaced.  Removing files [${_cmake_old_config_files_text}].")
        unset(_cmake_old_config_files_text)
        file(REMOVE ${_cmake_old_config_files})
      endif()
      unset(_cmake_old_config_files)
    endif()
    unset(_cmake_export_file_changed)
  endif()
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/cmake/gsl-2.7" TYPE FILE FILES "/home/aaa/gsl/build/CMakeFiles/Export/be3280bb442f4242bb46ea3e6d171e46/gsl-targets.cmake")
  if(CMAKE_INSTALL_CONFIG_NAME MATCHES "^([Dd][Ee][Bb][Uu][Gg])$")
    file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/cmake/gsl-2.7" TYPE FILE FILES "/home/aaa/gsl/build/CMakeFiles/Export/be3280bb442f4242bb46ea3e6d171e46/gsl-targets-debug.cmake")
  endif()
endif()

if(CMAKE_INSTALL_COMPONENT STREQUAL "gsl" OR NOT CMAKE_INSTALL_COMPONENT)
  file(INSTALL DESTINATION "${CMAKE_INSTALL_PREFIX}/lib/cmake/gsl-2.7" TYPE FILE FILES
    "/home/aaa/gsl/build/cmake/gsl-config.cmake"
    "/home/aaa/gsl/build/cmake/gsl-config-version.cmake"
    )
endif()

if(CMAKE_INSTALL_COMPONENT)
  set(CMAKE_INSTALL_MANIFEST "install_manifest_${CMAKE_INSTALL_COMPONENT}.txt")
else()
  set(CMAKE_INSTALL_MANIFEST "install_manifest.txt")
endif()

string(REPLACE ";" "\n" CMAKE_INSTALL_MANIFEST_CONTENT
       "${CMAKE_INSTALL_MANIFEST_FILES}")
file(WRITE "/home/aaa/gsl/build/${CMAKE_INSTALL_MANIFEST}"
     "${CMAKE_INSTALL_MANIFEST_CONTENT}")
