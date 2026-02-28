// Lean compiler output
// Module: NemS.Visibility.SemanticExternality
// Imports: public import Init public import NemS.Visibility.SelfEncoding public import NemS.Reduction.ER
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* lp_nems_NemS_Framework_SemanticExternality_toExternalDep(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_nems_NemS_Framework_SemanticExternality_toExternalDep(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_nems_NemS_Visibility_SelfEncoding(uint8_t builtin);
lean_object* initialize_nems_NemS_Reduction_ER(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_nems_NemS_Visibility_SemanticExternality(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_nems_NemS_Visibility_SelfEncoding(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_nems_NemS_Reduction_ER(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
