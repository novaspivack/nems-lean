// Lean compiler output
// Module: NemS.Examples.Toy
// Imports: public import Init public import NemS.Core.Trichotomy public import NemS.Reduction.ER
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
LEAN_EXPORT lean_object* lp_nems_NemS_Examples_unitFramework;
LEAN_EXPORT lean_object* lp_nems_NemS_Examples_boolFramework;
LEAN_EXPORT lean_object* lp_nems_NemS_Examples_trivialFramework;
LEAN_EXPORT lean_object* lp_nems_NemS_Examples_unitDep;
static lean_object* _init_lp_nems_NemS_Examples_trivialFramework() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_lp_nems_NemS_Examples_boolFramework() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_lp_nems_NemS_Examples_unitFramework() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_lp_nems_NemS_Examples_unitDep() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_nems_NemS_Core_Trichotomy(uint8_t builtin);
lean_object* initialize_nems_NemS_Reduction_ER(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_nems_NemS_Examples_Toy(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_nems_NemS_Core_Trichotomy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_nems_NemS_Reduction_ER(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_nems_NemS_Examples_trivialFramework = _init_lp_nems_NemS_Examples_trivialFramework();
lean_mark_persistent(lp_nems_NemS_Examples_trivialFramework);
lp_nems_NemS_Examples_boolFramework = _init_lp_nems_NemS_Examples_boolFramework();
lean_mark_persistent(lp_nems_NemS_Examples_boolFramework);
lp_nems_NemS_Examples_unitFramework = _init_lp_nems_NemS_Examples_unitFramework();
lean_mark_persistent(lp_nems_NemS_Examples_unitFramework);
lp_nems_NemS_Examples_unitDep = _init_lp_nems_NemS_Examples_unitDep();
lean_mark_persistent(lp_nems_NemS_Examples_unitDep);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
