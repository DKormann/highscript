// Lean compiler output
// Module: HighScript.Out
// Imports: Init HighScript.DSL
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
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*, lean_object*);
static lean_object* l_runHVM___closed__7;
static lean_object* l_runHVM___closed__4;
static lean_object* l_runHVM___closed__2;
LEAN_EXPORT lean_object* l_runHVM(lean_object*, lean_object*, lean_object*);
lean_object* l_compile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_writeHVM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_writeHVM(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_runHVM___closed__6;
static lean_object* l_runHVM___closed__1;
static lean_object* l_runHVM___closed__8;
static lean_object* l_runHVM___closed__9;
lean_object* l_IO_Process_output(lean_object*, lean_object*);
lean_object* l_IO_print___at_IO_println___spec__1(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
static lean_object* l_runHVM___closed__3;
static lean_object* l_runHVM___closed__5;
static lean_object* l_runHVM___closed__10;
static lean_object* l_runHVM___closed__11;
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_writeHVM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
x_6 = lean_io_prim_handle_mk(x_2, x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_compile(x_1, x_3);
x_10 = lean_io_prim_handle_put_str(x_7, x_9, x_8);
lean_dec(x_9);
lean_dec(x_7);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_3);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
return x_6;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_6);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_writeHVM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_writeHVM(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_runHVM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("out.hvm", 7, 7);
return x_1;
}
}
static lean_object* _init_l_runHVM___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_runHVM___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-C10", 4, 4);
return x_1;
}
}
static lean_object* _init_l_runHVM___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_runHVM___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_runHVM___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_runHVM___closed__1;
x_2 = l_runHVM___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_runHVM___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("run", 3, 3);
return x_1;
}
}
static lean_object* _init_l_runHVM___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_runHVM___closed__6;
x_2 = l_runHVM___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_runHVM___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_runHVM___closed__7;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_runHVM___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_runHVM___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hvm", 3, 3);
return x_1;
}
}
static lean_object* _init_l_runHVM___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l_runHVM___closed__2;
x_3 = l_runHVM___closed__10;
x_4 = l_runHVM___closed__8;
x_5 = l_runHVM___closed__9;
x_6 = 0;
x_7 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_1);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_runHVM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_runHVM___closed__1;
x_5 = l_writeHVM(x_1, x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_runHVM___closed__11;
x_8 = l_IO_Process_output(x_7, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_IO_print___at_IO_println___spec__1(x_11, x_10);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_HighScript_DSL(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HighScript_Out(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_HighScript_DSL(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_runHVM___closed__1 = _init_l_runHVM___closed__1();
lean_mark_persistent(l_runHVM___closed__1);
l_runHVM___closed__2 = _init_l_runHVM___closed__2();
lean_mark_persistent(l_runHVM___closed__2);
l_runHVM___closed__3 = _init_l_runHVM___closed__3();
lean_mark_persistent(l_runHVM___closed__3);
l_runHVM___closed__4 = _init_l_runHVM___closed__4();
lean_mark_persistent(l_runHVM___closed__4);
l_runHVM___closed__5 = _init_l_runHVM___closed__5();
lean_mark_persistent(l_runHVM___closed__5);
l_runHVM___closed__6 = _init_l_runHVM___closed__6();
lean_mark_persistent(l_runHVM___closed__6);
l_runHVM___closed__7 = _init_l_runHVM___closed__7();
lean_mark_persistent(l_runHVM___closed__7);
l_runHVM___closed__8 = _init_l_runHVM___closed__8();
lean_mark_persistent(l_runHVM___closed__8);
l_runHVM___closed__9 = _init_l_runHVM___closed__9();
lean_mark_persistent(l_runHVM___closed__9);
l_runHVM___closed__10 = _init_l_runHVM___closed__10();
lean_mark_persistent(l_runHVM___closed__10);
l_runHVM___closed__11 = _init_l_runHVM___closed__11();
lean_mark_persistent(l_runHVM___closed__11);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
