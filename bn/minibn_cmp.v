Require Import Clightdefs.

Require Import minibn. 

Local Open Scope Z_scope.

Definition _i : ident := 40%positive.
Definition _dmax : ident := 32%positive.
Definition ___compcert_va_int64 : ident := 16%positive.
Definition _atop : ident := 38%positive.
Definition _gt : ident := 46%positive.
Definition _main : ident := 54%positive.
Definition ___builtin_fmadd : ident := 24%positive.
Definition ___builtin_fmax : ident := 22%positive.
Definition ___compcert_va_float64 : ident := 17%positive.
Definition ___builtin_memcpy_aligned : ident := 8%positive.
Definition ___builtin_subl : ident := 5%positive.
Definition _BN_is_zero : ident := 50%positive.
Definition _ap : ident := 43%positive.
Definition ___builtin_va_arg : ident := 12%positive.
Definition _BN_is_one : ident := 53%positive.
Definition _lt : ident := 47%positive.
Definition ___builtin_annot_intval : ident := 10%positive.
Definition _bp : ident := 44%positive.
Definition ___builtin_negl : ident := 3%positive.
Definition ___builtin_write32_reversed : ident := 2%positive.
Definition ___builtin_write16_reversed : ident := 1%positive.
Definition _a : ident := 36%positive.
Definition _neg : ident := 31%positive.
Definition ___builtin_va_end : ident := 14%positive.
Definition ___builtin_mull : ident := 6%positive.
Definition ___builtin_fnmadd : ident := 26%positive.
Definition ___builtin_bswap32 : ident := 19%positive.
Definition _btop : ident := 39%positive.
Definition ___builtin_va_start : ident := 11%positive.
Definition _bn : ident := 49%positive.
Definition _b : ident := 37%positive.
Definition ___builtin_addl : ident := 4%positive.
Definition ___builtin_read16_reversed : ident := 28%positive.
Definition ___builtin_fabs : ident := 7%positive.
Definition _t2 : ident := 42%positive.
Definition ___builtin_fsqrt : ident := 21%positive.
Definition ___builtin_bswap : ident := 18%positive.
Definition ___builtin_annot : ident := 9%positive.
Definition _BN_abs_is_word : ident := 52%positive.
Definition _BN_ucmp : ident := 45%positive.
Definition _t1 : ident := 41%positive.
Definition ___builtin_va_copy : ident := 13%positive.
Definition ___builtin_fnmsub : ident := 27%positive.
Definition _top : ident := 33%positive.
Definition ___builtin_fmsub : ident := 25%positive.
Definition ___compcert_va_int32 : ident := 15%positive.
Definition _d : ident := 34%positive.
Definition ___builtin_read32_reversed : ident := 29%positive.
Definition _struct_bignum_st : ident := 35%positive.
Definition _flags : ident := 30%positive.
Definition ___builtin_fmin : ident := 23%positive.
Definition _w : ident := 51%positive.
Definition _BN_cmp : ident := 48%positive.
Definition ___builtin_bswap16 : ident := 20%positive.
(*
Definition t_struct_bignum_st :=
   (Tstruct _struct_bignum_st
     (Fcons _d (tptr tuint)
       (Fcons _top tint
         (Fcons _dmax tint (Fcons _neg tint (Fcons _flags tint Fnil)))))
     noattr).
*)
Definition f_BN_ucmp := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr t_struct_bignum_st)) ::
                (_b, (tptr t_struct_bignum_st)) :: nil);
  fn_vars := nil;
  fn_temps := ((_atop, tint) :: (_btop, tint) :: (_i, tint) ::
               (_t1, tuint) :: (_t2, tuint) :: (_ap, (tptr tuint)) ::
               (_bp, (tptr tuint)) :: (55%positive, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _atop
    (Efield
      (Ederef (Etempvar _a (tptr t_struct_bignum_st)) t_struct_bignum_st)
      _top tint))
  (Ssequence
    (Sset _btop
      (Efield
        (Ederef (Etempvar _b (tptr t_struct_bignum_st)) t_struct_bignum_st)
        _top tint))
    (Ssequence
      (Sset _i
        (Ebinop Osub (Etempvar _atop tint) (Etempvar _btop tint) tint))
      (Ssequence
        (Sifthenelse (Ebinop One (Etempvar _i tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Sreturn (Some (Etempvar _i tint)))
          Sskip)
        (Ssequence
          (Sset _ap
            (Efield
              (Ederef (Etempvar _a (tptr t_struct_bignum_st))
                t_struct_bignum_st) _d (tptr tuint)))
          (Ssequence
            (Sset _bp
              (Efield
                (Ederef (Etempvar _b (tptr t_struct_bignum_st))
                  t_struct_bignum_st) _d (tptr tuint)))
            (Ssequence
              (Ssequence
                (Sset _i
                  (Ebinop Osub (Etempvar _atop tint)
                    (Econst_int (Int.repr 1) tint) tint))
                (Sloop
                  (Ssequence
                    (Sifthenelse (Ebinop Oge (Etempvar _i tint)
                                   (Econst_int (Int.repr 0) tint) tint)
                      Sskip
                      Sbreak)
                    (Ssequence
                      (Sset _t1
                        (Ederef
                          (Ebinop Oadd (Etempvar _ap (tptr tuint))
                            (Etempvar _i tint) (tptr tuint)) tuint))
                      (Ssequence
                        (Sset _t2
                          (Ederef
                            (Ebinop Oadd (Etempvar _bp (tptr tuint))
                              (Etempvar _i tint) (tptr tuint)) tuint))
                        (Sifthenelse (Ebinop One (Etempvar _t1 tuint)
                                       (Etempvar _t2 tuint) tint)
                          (Ssequence
                            (Sifthenelse (Ebinop Ogt (Etempvar _t1 tuint)
                                           (Etempvar _t2 tuint) tint)
                              (Sset 55%positive
                                (Ecast (Econst_int (Int.repr 1) tint) tint))
                              (Sset 55%positive
                                (Ecast
                                  (Eunop Oneg (Econst_int (Int.repr 1) tint)
                                    tint) tint)))
                            (Sreturn (Some (Etempvar 55%positive tint))))
                          Sskip))))
                  (Sset _i
                    (Ebinop Osub (Etempvar _i tint)
                      (Econst_int (Int.repr 1) tint) tint))))
              (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))
|}.

Definition f_BN_cmp := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr t_struct_bignum_st)) ::
                (_b, (tptr t_struct_bignum_st)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_gt, tint) :: (_lt, tint) :: (_t1, tuint) ::
               (_t2, tuint) :: (56%positive, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _a (tptr t_struct_bignum_st))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sset 56%positive (Econst_int (Int.repr 1) tint))
      (Ssequence
        (Sset 56%positive
          (Ecast
            (Ebinop Oeq (Etempvar _b (tptr t_struct_bignum_st))
              (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
            tbool))
        (Sset 56%positive (Ecast (Etempvar 56%positive tbool) tint))))
    (Sifthenelse (Etempvar 56%positive tint)
      (Sifthenelse (Ebinop One (Etempvar _a (tptr t_struct_bignum_st))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
        (Sifthenelse (Ebinop One (Etempvar _b (tptr t_struct_bignum_st))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Sreturn (Some (Econst_int (Int.repr 1) tint)))
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
      Sskip))
  (Ssequence
    (Sifthenelse (Ebinop One
                   (Efield
                     (Ederef (Etempvar _a (tptr t_struct_bignum_st))
                       t_struct_bignum_st) _neg tint)
                   (Efield
                     (Ederef (Etempvar _b (tptr t_struct_bignum_st))
                       t_struct_bignum_st) _neg tint) tint)
      (Ssequence
        (Sifthenelse (Efield
                       (Ederef (Etempvar _a (tptr t_struct_bignum_st))
                         t_struct_bignum_st) _neg tint)
          (Sreturn (Some (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
          Sskip)
        (Sreturn (Some (Econst_int (Int.repr 1) tint))))
      Sskip)
    (Ssequence
      (Sifthenelse (Ebinop Oeq
                     (Efield
                       (Ederef (Etempvar _a (tptr t_struct_bignum_st))
                         t_struct_bignum_st) _neg tint)
                     (Econst_int (Int.repr 0) tint) tint)
        (Ssequence
          (Sset _gt (Econst_int (Int.repr 1) tint))
          (Sset _lt (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)))
        (Ssequence
          (Sset _gt (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
          (Sset _lt (Econst_int (Int.repr 1) tint))))
      (Ssequence
        (Sifthenelse (Ebinop Ogt
                       (Efield
                         (Ederef (Etempvar _a (tptr t_struct_bignum_st))
                           t_struct_bignum_st) _top tint)
                       (Efield
                         (Ederef (Etempvar _b (tptr t_struct_bignum_st))
                           t_struct_bignum_st) _top tint) tint)
          (Sreturn (Some (Etempvar _gt tint)))
          Sskip)
        (Ssequence
          (Sifthenelse (Ebinop Olt
                         (Efield
                           (Ederef (Etempvar _a (tptr t_struct_bignum_st))
                             t_struct_bignum_st) _top tint)
                         (Efield
                           (Ederef (Etempvar _b (tptr t_struct_bignum_st))
                             t_struct_bignum_st) _top tint) tint)
            (Sreturn (Some (Etempvar _lt tint)))
            Sskip)
          (Ssequence
            (Ssequence
              (Sset _i
                (Ebinop Osub
                  (Efield
                    (Ederef (Etempvar _a (tptr t_struct_bignum_st))
                      t_struct_bignum_st) _top tint)
                  (Econst_int (Int.repr 1) tint) tint))
              (Sloop
                (Ssequence
                  (Sifthenelse (Ebinop Oge (Etempvar _i tint)
                                 (Econst_int (Int.repr 0) tint) tint)
                    Sskip
                    Sbreak)
                  (Ssequence
                    (Sset _t1
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef (Etempvar _a (tptr t_struct_bignum_st))
                              t_struct_bignum_st) _d (tptr tuint))
                          (Etempvar _i tint) (tptr tuint)) tuint))
                    (Ssequence
                      (Sset _t2
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef (Etempvar _b (tptr t_struct_bignum_st))
                                t_struct_bignum_st) _d (tptr tuint))
                            (Etempvar _i tint) (tptr tuint)) tuint))
                      (Ssequence
                        (Sifthenelse (Ebinop Ogt (Etempvar _t1 tuint)
                                       (Etempvar _t2 tuint) tint)
                          (Sreturn (Some (Etempvar _gt tint)))
                          Sskip)
                        (Sifthenelse (Ebinop Olt (Etempvar _t1 tuint)
                                       (Etempvar _t2 tuint) tint)
                          (Sreturn (Some (Etempvar _lt tint)))
                          Sskip)))))
                (Sset _i
                  (Ebinop Osub (Etempvar _i tint)
                    (Econst_int (Int.repr 1) tint) tint))))
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))
|}.

Definition f_BN_is_zero := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr t_struct_bignum_st)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oeq
                 (Efield
                   (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                     t_struct_bignum_st) _top tint)
                 (Econst_int (Int.repr 0) tint) tint)))
|}.
(*
Definition f_BN_abs_is_word := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr t_struct_bignum_st)) :: (_w, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sswitch (Efield
           (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
             t_struct_bignum_st) _top tint)
  (LScase (Some (Int.repr 1))
    (Sreturn (Some (Ebinop Oeq
                     (Ederef
                       (Ebinop Oadd
                         (Efield
                           (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                             t_struct_bignum_st) _d (tptr tuint))
                         (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
                     (Etempvar _w tuint) tint)))
    (LScase (Some (Int.repr 0))
      (Sreturn (Some (Ebinop Oeq (Etempvar _w tuint)
                       (Econst_int (Int.repr 0) tint) tint)))
      (LScase None (Sreturn (Some (Econst_int (Int.repr 0) tint))) ))))
|}.
*)
Definition f_BN_is_one := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr t_struct_bignum_st)) :: nil);
  fn_vars := nil;
  fn_temps := ((58%positive, tint) :: (57%positive, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Efield
                   (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                     t_struct_bignum_st) _neg tint)
                 (Econst_int (Int.repr 0) tint) tint)
    (Ssequence
      (Ssequence
        (Scall (Some 58%positive)
          (Evar _BN_abs_is_word (Tfunction
                                  (Tcons (tptr t_struct_bignum_st)
                                    (Tcons tuint Tnil)) tint cc_default))
          ((Etempvar _bn (tptr t_struct_bignum_st)) ::
           (Econst_int (Int.repr 1) tint) :: nil))
        (Sset 57%positive (Ecast (Etempvar 58%positive tint) tbool)))
      (Sset 57%positive (Ecast (Etempvar 57%positive tbool) tint)))
    (Sset 57%positive (Econst_int (Int.repr 0) tint)))
  (Sreturn (Some (Etempvar 57%positive tint))))
|}.

Definition prog : Clight.program := {|
prog_defs :=
((___builtin_fabs,
   Gfun(External (EF_builtin ___builtin_fabs
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin ___builtin_memcpy_aligned
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin ___builtin_annot
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin ___builtin_annot_intval
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin ___builtin_va_start
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin ___builtin_va_arg
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin ___builtin_va_copy
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin ___builtin_va_end
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external ___compcert_va_int32
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external ___compcert_va_int64
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external ___compcert_va_float64
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin ___builtin_bswap
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin ___builtin_bswap32
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin ___builtin_bswap16
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin ___builtin_fsqrt
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin ___builtin_fmax
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin ___builtin_fmin
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin ___builtin_fmadd
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin ___builtin_fmsub
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin ___builtin_fnmadd
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin ___builtin_fnmsub
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin ___builtin_read16_reversed
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin ___builtin_read32_reversed
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin ___builtin_write16_reversed
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin ___builtin_write32_reversed
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) :: (_BN_ucmp, Gfun(Internal f_BN_ucmp)) ::
 (_BN_cmp, Gfun(Internal f_BN_cmp)) ::
 (_BN_is_zero, Gfun(Internal f_BN_is_zero)) ::
(* (_BN_abs_is_word, Gfun(Internal f_BN_abs_is_word)) ::*)
 (_BN_is_one, Gfun(Internal f_BN_is_one)) :: nil);
prog_main := _main
|}.

