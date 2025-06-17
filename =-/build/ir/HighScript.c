// Lean compiler output
// Module: highscript
// Imports: Init HighScript.DSL HighScript.Out
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
lean_object* l_runHVM(lean_object*, lean_object*, lean_object*);
lean_object* l_Expr_fn(lean_object*, lean_object*, lean_object*);
static lean_object* l_runmain___closed__1;
LEAN_EXPORT lean_object* l_runmain(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_runmain___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("main", 4, 4);
return x_1;
}
}
LEAN_EXPORT lean_object* l_runmain(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_runmain___closed__1;
lean_inc(x_1);
x_5 = l_Expr_fn(x_1, x_4, x_2);
x_6 = l_runHVM(x_1, x_5, x_3);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HighScript_DSL(uint8_t builtin, lean_object*);
lean_object* initialize_HighScript_Out(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_highscript(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HighScript_DSL(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HighScript_Out(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_runmain___closed__1 = _init_l_runmain___closed__1();
lean_mark_persistent(l_runmain___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
