Require Import Clightdefs.

Local Open Scope Z_scope.

Definition _max : ident := 65%positive.
Definition _BN_is_zero : ident := 40%positive.
Definition ___compcert_va_int64 : ident := 16%positive.
Definition _d : ident := 38%positive.
Definition _BN_free : ident := 46%positive.
Definition _BN_set_word : ident := 69%positive.
Definition _bits : ident := 62%positive.
Definition _bn_wexpand : ident := 54%positive.
Definition ___builtin_fmax : ident := 22%positive.
Definition ___builtin_va_arg : ident := 12%positive.
Definition _l : ident := 63%positive.
Definition ___builtin_annot_intval : ident := 10%positive.
Definition _BN_new : ident := 44%positive.
Definition ___builtin_negl : ident := 3%positive.
Definition ___builtin_write32_reversed : ident := 2%positive.
Definition ___builtin_write16_reversed : ident := 1%positive.
Definition _free : ident := 31%positive.
Definition _bn_correct_top : ident := 79%positive.
Definition _BN_is_negative : ident := 72%positive.
Definition _src : ident := 49%positive.
Definition _BN_num_bits : ident := 66%positive.
Definition _out : ident := 59%positive.
Definition ___builtin_addl : ident := 4%positive.
Definition _tmp_top : ident := 78%positive.
Definition _BN_zero : ident := 68%positive.
Definition _BN_value_one : ident := 58%positive.
Definition ___builtin_read16_reversed : ident := 28%positive.
Definition ___builtin_fabs : ident := 7%positive.
Definition ___builtin_fsqrt : ident := 21%positive.
Definition ___builtin_bswap : ident := 18%positive.
Definition _BN_init : ident := 45%positive.
Definition _bits__1 : ident := 80%positive.
Definition ___builtin_va_copy : ident := 13%positive.
Definition ___builtin_fnmsub : ident := 27%positive.
Definition _main : ident := 82%positive.
Definition _memset : ident := 33%positive.
Definition _data_one : ident := 56%positive.
Definition ___builtin_fmsub : ident := 25%positive.
Definition ___compcert_va_int32 : ident := 15%positive.
Definition _in : ident := 60%positive.
Definition ___builtin_bswap16 : ident := 20%positive.
Definition _memcpy : ident := 32%positive.
Definition _BN_one : ident := 70%positive.
Definition ___builtin_fmadd : ident := 24%positive.
Definition _BN_num_bytes : ident := 67%positive.
Definition ___compcert_va_float64 : ident := 17%positive.
Definition ___builtin_memcpy_aligned : ident := 8%positive.
Definition ___builtin_subl : ident := 5%positive.
Definition _words : ident := 73%positive.
Definition _copy : ident := 50%positive.
Definition _bn : ident := 43%positive.
Definition _a : ident := 74%positive.
Definition _dest : ident := 53%positive.
Definition _should_free : ident := 47%positive.
Definition _const_one : ident := 57%positive.
Definition _dmax : ident := 36%positive.
Definition ___builtin_va_end : ident := 14%positive.
Definition ___builtin_mull : ident := 6%positive.
Definition ___builtin_fnmadd : ident := 26%positive.
Definition ___builtin_bswap32 : ident := 19%positive.
Definition _struct_bignum_st : ident := 39%positive.
Definition _BN_with_flags : ident := 61%positive.
Definition ___builtin_va_start : ident := 11%positive.
Definition _top : ident := 37%positive.
Definition _bn_expand : ident := 81%positive.
Definition _BN_set_negative : ident := 76%positive.
Definition _mallocN : ident := 42%positive.
Definition ___builtin_annot : ident := 9%positive.
Definition _BN_num_bits_word : ident := 64%positive.
Definition _BN_dup : ident := 52%positive.
Definition _OPENSSL_cleanse : ident := 41%positive.
Definition _ftl : ident := 77%positive.
Definition _value : ident := 71%positive.
Definition _sign : ident := 75%positive.
Definition _flags : ident := 34%positive.
Definition ___builtin_read32_reversed : ident := 29%positive.
Definition _BN_clear : ident := 55%positive.
Definition _neg : ident := 35%positive.
Definition _malloc : ident := 30%positive.
Definition ___builtin_fmin : ident := 23%positive.
Definition _BN_copy : ident := 51%positive.
Definition _BN_clear_free : ident := 48%positive.
Definition _copy' : ident := 85%positive.
Definition _bn' : ident := 83%positive.
Definition _a' : ident := 94%positive.

Definition t_struct_bignum_st :=
   (Tstruct _struct_bignum_st
     (Fcons _d (tptr tuint)
       (Fcons _top tint
         (Fcons _dmax tint (Fcons _neg tint (Fcons _flags tint Fnil)))))
     noattr).

Definition f_BN_new := {|
  fn_return := (tptr t_struct_bignum_st);
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_bn, (tptr t_struct_bignum_st)) :: (_bn', (tptr tvoid)) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _bn')
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Econst_int (Int.repr 20) tuint) :: nil))
    (Sset _bn (Etempvar _bn' (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _bn (tptr t_struct_bignum_st))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
      Sskip)
    (Ssequence
      (Scall None
        (Evar _memset (Tfunction
                        (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                        (tptr tvoid) cc_default))
        ((Etempvar _bn (tptr t_struct_bignum_st)) ::
         (Econst_int (Int.repr 0) tint) ::
         (Econst_int (Int.repr 20) tuint) :: nil))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
              t_struct_bignum_st) _flags tint)
          (Econst_int (Int.repr 1) tint))
        (Sreturn (Some (Etempvar _bn (tptr t_struct_bignum_st))))))))
|}.

Definition f_BN_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr t_struct_bignum_st)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _memset (Tfunction
                  (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                  (tptr tvoid) cc_default))
  ((Etempvar _bn (tptr t_struct_bignum_st)) ::
   (Econst_int (Int.repr 0) tint) :: (Econst_int (Int.repr 20) tuint) :: nil))
|}.

Definition f_BN_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr t_struct_bignum_st)) :: nil);
  fn_vars := nil;
  fn_temps := ((84%positive, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _bn (tptr t_struct_bignum_st))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop One
                     (Efield
                       (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                         t_struct_bignum_st) _d (tptr tuint))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Ssequence
          (Sset 84%positive
            (Ecast
              (Ebinop Oeq
                (Ebinop Oand
                  (Efield
                    (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                      t_struct_bignum_st) _flags tint)
                  (Econst_int (Int.repr 2) tint) tint)
                (Econst_int (Int.repr 0) tint) tint) tbool))
          (Sset 84%positive (Ecast (Etempvar 84%positive tbool) tint)))
        (Sset 84%positive (Econst_int (Int.repr 0) tint)))
      (Sifthenelse (Etempvar 84%positive tint)
        (Scall None
          (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
          ((Efield
             (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
               t_struct_bignum_st) _d (tptr tuint)) :: nil))
        Sskip))
    (Sifthenelse (Ebinop Oand
                   (Efield
                     (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                       t_struct_bignum_st) _flags tint)
                   (Econst_int (Int.repr 1) tint) tint)
      (Scall None
        (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
        ((Etempvar _bn (tptr t_struct_bignum_st)) :: nil))
      (Sassign
        (Efield
          (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
            t_struct_bignum_st) _d (tptr tuint))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))))
|}.

Definition f_BN_clear_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr t_struct_bignum_st)) :: nil);
  fn_vars := nil;
  fn_temps := ((_should_free, tschar) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _bn (tptr t_struct_bignum_st))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Sifthenelse (Ebinop One
                   (Efield
                     (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                       t_struct_bignum_st) _d (tptr tuint))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Scall None
          (Evar _OPENSSL_cleanse (Tfunction
                                   (Tcons (tptr tvoid) (Tcons tuint Tnil))
                                   tvoid cc_default))
          ((Efield
             (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
               t_struct_bignum_st) _d (tptr tuint)) ::
           (Ebinop Omul
             (Efield
               (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                 t_struct_bignum_st) _dmax tint)
             (Econst_int (Int.repr 4) tuint) tuint) :: nil))
        (Sifthenelse (Ebinop Oeq
                       (Ebinop Oand
                         (Efield
                           (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                             t_struct_bignum_st) _flags tint)
                         (Econst_int (Int.repr 2) tint) tint)
                       (Econst_int (Int.repr 0) tint) tint)
          (Scall None
            (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                          cc_default))
            ((Efield
               (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                 t_struct_bignum_st) _d (tptr tuint)) :: nil))
          Sskip))
      Sskip)
    (Ssequence
      (Sset _should_free
        (Ecast
          (Ebinop One
            (Ebinop Oand
              (Efield
                (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                  t_struct_bignum_st) _flags tint)
              (Econst_int (Int.repr 1) tint) tint)
            (Econst_int (Int.repr 0) tint) tint) tschar))
      (Ssequence
        (Scall None
          (Evar _OPENSSL_cleanse (Tfunction
                                   (Tcons (tptr tvoid) (Tcons tuint Tnil))
                                   tvoid cc_default))
          ((Etempvar _bn (tptr t_struct_bignum_st)) ::
           (Econst_int (Int.repr 20) tuint) :: nil))
        (Sifthenelse (Etempvar _should_free tschar)
          (Scall None
            (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                          cc_default))
            ((Etempvar _bn (tptr t_struct_bignum_st)) :: nil))
          Sskip)))))
|}.

Definition f_BN_dup := {|
  fn_return := (tptr t_struct_bignum_st);
  fn_callconv := cc_default;
  fn_params := ((_src, (tptr t_struct_bignum_st)) :: nil);
  fn_vars := nil;
  fn_temps := ((_copy, (tptr t_struct_bignum_st)) ::
               (86%positive, (tptr t_struct_bignum_st)) ::
               (_copy', (tptr t_struct_bignum_st)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _src (tptr t_struct_bignum_st))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
    Sskip)
  (Ssequence
    (Ssequence
      (Scall (Some _copy')
        (Evar _BN_new (Tfunction Tnil (tptr t_struct_bignum_st) cc_default))
        nil)
      (Sset _copy (Etempvar _copy' (tptr t_struct_bignum_st))))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _copy (tptr t_struct_bignum_st))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
        Sskip)
      (Ssequence
        (Ssequence
          (Scall (Some 86%positive)
            (Evar _BN_copy (Tfunction
                             (Tcons (tptr t_struct_bignum_st)
                               (Tcons (tptr t_struct_bignum_st) Tnil))
                             (tptr t_struct_bignum_st) cc_default))
            ((Etempvar _copy (tptr t_struct_bignum_st)) ::
             (Etempvar _src (tptr t_struct_bignum_st)) :: nil))
          (Sifthenelse (Eunop Onotbool
                         (Etempvar 86%positive (tptr t_struct_bignum_st))
                         tint)
            (Ssequence
              (Scall None
                (Evar _BN_free (Tfunction
                                 (Tcons (tptr t_struct_bignum_st) Tnil) tvoid
                                 cc_default))
                ((Etempvar _copy (tptr t_struct_bignum_st)) :: nil))
              (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)))))
            Sskip))
        (Sreturn (Some (Etempvar _copy (tptr t_struct_bignum_st))))))))
|}.

Definition f_BN_copy := {|
  fn_return := (tptr t_struct_bignum_st);
  fn_callconv := cc_default;
  fn_params := ((_dest, (tptr t_struct_bignum_st)) ::
                (_src, (tptr t_struct_bignum_st)) :: nil);
  fn_vars := nil;
  fn_temps := ((87%positive, (tptr t_struct_bignum_st)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _src (tptr t_struct_bignum_st))
                 (Etempvar _dest (tptr t_struct_bignum_st)) tint)
    (Sreturn (Some (Etempvar _dest (tptr t_struct_bignum_st))))
    Sskip)
  (Ssequence
    (Ssequence
      (Scall (Some 87%positive)
        (Evar _bn_wexpand (Tfunction
                            (Tcons (tptr t_struct_bignum_st)
                              (Tcons tuint Tnil)) (tptr t_struct_bignum_st)
                            cc_default))
        ((Etempvar _dest (tptr t_struct_bignum_st)) ::
         (Efield
           (Ederef (Etempvar _src (tptr t_struct_bignum_st))
             t_struct_bignum_st) _top tint) :: nil))
      (Sifthenelse (Ebinop Oeq
                     (Etempvar 87%positive (tptr t_struct_bignum_st))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
        Sskip))
    (Ssequence
      (Scall None
        (Evar _memcpy (Tfunction
                        (Tcons (tptr tvoid)
                          (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                        (tptr tvoid) cc_default))
        ((Efield
           (Ederef (Etempvar _dest (tptr t_struct_bignum_st))
             t_struct_bignum_st) _d (tptr tuint)) ::
         (Efield
           (Ederef (Etempvar _src (tptr t_struct_bignum_st))
             t_struct_bignum_st) _d (tptr tuint)) ::
         (Ebinop Omul (Econst_int (Int.repr 4) tuint)
           (Efield
             (Ederef (Etempvar _src (tptr t_struct_bignum_st))
               t_struct_bignum_st) _top tint) tuint) :: nil))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _dest (tptr t_struct_bignum_st))
              t_struct_bignum_st) _top tint)
          (Efield
            (Ederef (Etempvar _src (tptr t_struct_bignum_st))
              t_struct_bignum_st) _top tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _dest (tptr t_struct_bignum_st))
                t_struct_bignum_st) _neg tint)
            (Efield
              (Ederef (Etempvar _src (tptr t_struct_bignum_st))
                t_struct_bignum_st) _neg tint))
          (Sreturn (Some (Etempvar _dest (tptr t_struct_bignum_st)))))))))
|}.

Definition f_BN_clear := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr t_struct_bignum_st)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One
                 (Efield
                   (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                     t_struct_bignum_st) _d (tptr tuint))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Scall None
      (Evar _memset (Tfunction
                      (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                      (tptr tvoid) cc_default))
      ((Efield
         (Ederef (Etempvar _bn (tptr t_struct_bignum_st)) t_struct_bignum_st)
         _d (tptr tuint)) :: (Econst_int (Int.repr 0) tint) ::
       (Ebinop Omul
         (Efield
           (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
             t_struct_bignum_st) _dmax tint) (Econst_int (Int.repr 4) tuint)
         tuint) :: nil))
    Sskip)
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _bn (tptr t_struct_bignum_st)) t_struct_bignum_st)
        _top tint) (Econst_int (Int.repr 0) tint))
    (Sassign
      (Efield
        (Ederef (Etempvar _bn (tptr t_struct_bignum_st)) t_struct_bignum_st)
        _neg tint) (Econst_int (Int.repr 0) tint))))
|}.

Definition v_data_one := {|
  gvar_info := tuint;
  gvar_init := (Init_int32 (Int.repr 1) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_const_one := {|
  gvar_info := t_struct_bignum_st;
  gvar_init := (Init_addrof _data_one (Int.repr 0) ::
                Init_int32 (Int.repr 1) :: Init_int32 (Int.repr 1) ::
                Init_int32 (Int.repr 0) :: Init_int32 (Int.repr 2) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_BN_value_one := {|
  fn_return := (tptr t_struct_bignum_st);
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eaddrof (Evar _const_one t_struct_bignum_st)
                 (tptr t_struct_bignum_st))))
|}.

Definition f_BN_with_flags := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr t_struct_bignum_st)) ::
                (_in, (tptr t_struct_bignum_st)) :: (_flags, tint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _memcpy (Tfunction
                    (Tcons (tptr tvoid)
                      (Tcons (tptr tvoid) (Tcons tuint Tnil))) (tptr tvoid)
                    cc_default))
    ((Etempvar _out (tptr t_struct_bignum_st)) ::
     (Etempvar _in (tptr t_struct_bignum_st)) ::
     (Econst_int (Int.repr 20) tuint) :: nil))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _out (tptr t_struct_bignum_st)) t_struct_bignum_st)
        _flags tint)
      (Ebinop Oand
        (Efield
          (Ederef (Etempvar _out (tptr t_struct_bignum_st))
            t_struct_bignum_st) _flags tint)
        (Eunop Onotint (Econst_int (Int.repr 1) tint) tint) tint))
    (Sassign
      (Efield
        (Ederef (Etempvar _out (tptr t_struct_bignum_st)) t_struct_bignum_st)
        _flags tint)
      (Ebinop Oor
        (Efield
          (Ederef (Etempvar _out (tptr t_struct_bignum_st))
            t_struct_bignum_st) _flags tint)
        (Ebinop Oor (Econst_int (Int.repr 2) tint) (Etempvar _flags tint)
          tint) tint))))
|}.

Definition v_bits := {|
  gvar_info := (tarray tuchar 256);
  gvar_init := (Init_int8 (Int.repr 0) :: Init_int8 (Int.repr 1) ::
                Init_int8 (Int.repr 2) :: Init_int8 (Int.repr 2) ::
                Init_int8 (Int.repr 3) :: Init_int8 (Int.repr 3) ::
                Init_int8 (Int.repr 3) :: Init_int8 (Int.repr 3) ::
                Init_int8 (Int.repr 4) :: Init_int8 (Int.repr 4) ::
                Init_int8 (Int.repr 4) :: Init_int8 (Int.repr 4) ::
                Init_int8 (Int.repr 4) :: Init_int8 (Int.repr 4) ::
                Init_int8 (Int.repr 4) :: Init_int8 (Int.repr 4) ::
                Init_int8 (Int.repr 5) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 5) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 5) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 5) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 5) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 5) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 5) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 5) :: Init_int8 (Int.repr 5) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 6) :: Init_int8 (Int.repr 6) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 7) :: Init_int8 (Int.repr 7) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) ::
                Init_int8 (Int.repr 8) :: Init_int8 (Int.repr 8) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_BN_num_bits_word := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_l, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sifthenelse (Ebinop Oand (Etempvar _l tuint)
               (Econst_int (Int.repr (-65536)) tuint) tuint)
  (Sifthenelse (Ebinop Oand (Etempvar _l tuint)
                 (Econst_int (Int.repr (-16777216)) tuint) tuint)
    (Sreturn (Some (Ebinop Oadd
                     (Ederef
                       (Ebinop Oadd (Evar _bits (tarray tuchar 256))
                         (Ecast
                           (Ebinop Oshr (Etempvar _l tuint)
                             (Econst_int (Int.repr 24) tint) tuint) tint)
                         (tptr tuchar)) tuchar)
                     (Econst_int (Int.repr 24) tint) tint)))
    (Sreturn (Some (Ebinop Oadd
                     (Ederef
                       (Ebinop Oadd (Evar _bits (tarray tuchar 256))
                         (Ecast
                           (Ebinop Oshr (Etempvar _l tuint)
                             (Econst_int (Int.repr 16) tint) tuint) tint)
                         (tptr tuchar)) tuchar)
                     (Econst_int (Int.repr 16) tint) tint))))
  (Sifthenelse (Ebinop Oand (Etempvar _l tuint)
                 (Econst_int (Int.repr 65280) tint) tuint)
    (Sreturn (Some (Ebinop Oadd
                     (Ederef
                       (Ebinop Oadd (Evar _bits (tarray tuchar 256))
                         (Ecast
                           (Ebinop Oshr (Etempvar _l tuint)
                             (Econst_int (Int.repr 8) tint) tuint) tint)
                         (tptr tuchar)) tuchar)
                     (Econst_int (Int.repr 8) tint) tint)))
    (Sreturn (Some (Ederef
                     (Ebinop Oadd (Evar _bits (tarray tuchar 256))
                       (Ecast (Etempvar _l tuint) tint) (tptr tuchar))
                     tuchar)))))
|}.

Definition f_BN_num_bits := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr t_struct_bignum_st)) :: nil);
  fn_vars := nil;
  fn_temps := ((_max, tint) :: (89%positive, tuint) :: (88%positive, tint) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _max
    (Ebinop Osub
      (Efield
        (Ederef (Etempvar _bn (tptr t_struct_bignum_st)) t_struct_bignum_st)
        _top tint) (Econst_int (Int.repr 1) tint) tint))
  (Ssequence
    (Ssequence
      (Scall (Some 88%positive)
        (Evar _BN_is_zero (Tfunction (Tcons (tptr t_struct_bignum_st) Tnil)
                            tint cc_default))
        ((Etempvar _bn (tptr t_struct_bignum_st)) :: nil))
      (Sifthenelse (Etempvar 88%positive tint)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        Sskip))
    (Ssequence
      (Scall (Some 89%positive)
        (Evar _BN_num_bits_word (Tfunction (Tcons tuint Tnil) tuint
                                  cc_default))
        ((Ederef
           (Ebinop Oadd
             (Efield
               (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                 t_struct_bignum_st) _d (tptr tuint)) (Etempvar _max tint)
             (tptr tuint)) tuint) :: nil))
      (Sreturn (Some (Ebinop Oadd
                       (Ebinop Omul (Etempvar _max tint)
                         (Econst_int (Int.repr 32) tint) tint)
                       (Etempvar 89%positive tuint) tuint))))))
|}.

Definition f_BN_num_bytes := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr t_struct_bignum_st)) :: nil);
  fn_vars := nil;
  fn_temps := ((90%positive, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some 90%positive)
    (Evar _BN_num_bits (Tfunction (Tcons (tptr t_struct_bignum_st) Tnil)
                         tuint cc_default))
    ((Etempvar _bn (tptr t_struct_bignum_st)) :: nil))
  (Sreturn (Some (Ebinop Odiv
                   (Ebinop Oadd (Etempvar 90%positive tuint)
                     (Econst_int (Int.repr 7) tint) tuint)
                   (Econst_int (Int.repr 8) tint) tuint))))
|}.

Definition f_BN_zero := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr t_struct_bignum_st)) :: nil);
  fn_vars := nil;
  fn_temps := ((91%positive, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset 91%positive (Econst_int (Int.repr 0) tint))
    (Sassign
      (Efield
        (Ederef (Etempvar _bn (tptr t_struct_bignum_st)) t_struct_bignum_st)
        _neg tint) (Etempvar 91%positive tint)))
  (Sassign
    (Efield
      (Ederef (Etempvar _bn (tptr t_struct_bignum_st)) t_struct_bignum_st)
      _top tint) (Ecast (Etempvar 91%positive tint) tint)))
|}.

Definition f_BN_one := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr t_struct_bignum_st)) :: nil);
  fn_vars := nil;
  fn_temps := ((92%positive, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some 92%positive)
    (Evar _BN_set_word (Tfunction
                         (Tcons (tptr t_struct_bignum_st) (Tcons tuint Tnil))
                         tint cc_default))
    ((Etempvar _bn (tptr t_struct_bignum_st)) ::
     (Econst_int (Int.repr 1) tint) :: nil))
  (Sreturn (Some (Etempvar 92%positive tint))))
|}.

Definition f_BN_set_word := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr t_struct_bignum_st)) :: (_value, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((93%positive, (tptr t_struct_bignum_st)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _value tuint)
                 (Econst_int (Int.repr 0) tint) tint)
    (Ssequence
      (Scall None
        (Evar _BN_zero (Tfunction (Tcons (tptr t_struct_bignum_st) Tnil)
                         tvoid cc_default))
        ((Etempvar _bn (tptr t_struct_bignum_st)) :: nil))
      (Sreturn (Some (Econst_int (Int.repr 1) tint))))
    Sskip)
  (Ssequence
    (Ssequence
      (Scall (Some 93%positive)
        (Evar _bn_wexpand (Tfunction
                            (Tcons (tptr t_struct_bignum_st)
                              (Tcons tuint Tnil)) (tptr t_struct_bignum_st)
                            cc_default))
        ((Etempvar _bn (tptr t_struct_bignum_st)) ::
         (Econst_int (Int.repr 1) tint) :: nil))
      (Sifthenelse (Ebinop Oeq
                     (Etempvar 93%positive (tptr t_struct_bignum_st))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        Sskip))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
            t_struct_bignum_st) _neg tint) (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                  t_struct_bignum_st) _d (tptr tuint))
              (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
          (Etempvar _value tuint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                t_struct_bignum_st) _top tint)
            (Econst_int (Int.repr 1) tint))
          (Sreturn (Some (Econst_int (Int.repr 1) tint))))))))
|}.

Definition f_BN_is_negative := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr t_struct_bignum_st)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop One
                 (Efield
                   (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                     t_struct_bignum_st) _neg tint)
                 (Econst_int (Int.repr 0) tint) tint)))
|}.

Definition f_bn_wexpand := {|
  fn_return := (tptr t_struct_bignum_st);
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr t_struct_bignum_st)) :: (_words, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_a, (tptr tuint)) :: (_a', (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Ole (Etempvar _words tuint)
                 (Ecast
                   (Efield
                     (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                       t_struct_bignum_st) _dmax tint) tuint) tint)
    (Sreturn (Some (Etempvar _bn (tptr t_struct_bignum_st))))
    Sskip)
  (Ssequence
    (Sifthenelse (Ebinop Ogt (Etempvar _words tuint)
                   (Ebinop Odiv (Econst_int (Int.repr 2147483647) tint)
                     (Ebinop Omul (Econst_int (Int.repr 4) tint)
                       (Econst_int (Int.repr 32) tint) tint) tint) tint)
      (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
      Sskip)
    (Ssequence
      (Sifthenelse (Ebinop Oand
                     (Efield
                       (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                         t_struct_bignum_st) _flags tint)
                     (Econst_int (Int.repr 2) tint) tint)
        (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
        Sskip)
      (Ssequence
        (Ssequence
          (Scall (Some _a')
            (Evar _mallocN (Tfunction (Tcons tint Tnil) (tptr tvoid)
                             cc_default))
            ((Ebinop Omul (Econst_int (Int.repr 4) tuint)
               (Etempvar _words tuint) tuint) :: nil))
          (Sset _a (Ecast (Etempvar _a' (tptr tvoid)) (tptr tuint))))
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _a (tptr tuint))
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                         tint)
            (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid))))
            Sskip)
          (Ssequence
            (Scall None
              (Evar _memcpy (Tfunction
                              (Tcons (tptr tvoid)
                                (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                              (tptr tvoid) cc_default))
              ((Etempvar _a (tptr tuint)) ::
               (Efield
                 (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                   t_struct_bignum_st) _d (tptr tuint)) ::
               (Ebinop Omul (Econst_int (Int.repr 4) tuint)
                 (Efield
                   (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                     t_struct_bignum_st) _top tint) tuint) :: nil))
            (Ssequence
              (Sifthenelse (Efield
                             (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                               t_struct_bignum_st) _d (tptr tuint))
                (Scall None
                  (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                cc_default))
                  ((Efield
                     (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                       t_struct_bignum_st) _d (tptr tuint)) :: nil))
                Sskip)
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                      t_struct_bignum_st) _d (tptr tuint))
                  (Etempvar _a (tptr tuint)))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                        t_struct_bignum_st) _dmax tint)
                    (Etempvar _words tuint))
                  (Sreturn (Some (Etempvar _bn (tptr t_struct_bignum_st)))))))))))))
|}.

Definition f_BN_set_negative := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr t_struct_bignum_st)) :: (_sign, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((96%positive, tint) :: (95%positive, tint) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Etempvar _sign tint)
    (Ssequence
      (Ssequence
        (Scall (Some 96%positive)
          (Evar _BN_is_zero (Tfunction (Tcons (tptr t_struct_bignum_st) Tnil)
                              tint cc_default))
          ((Etempvar _bn (tptr t_struct_bignum_st)) :: nil))
        (Sset 95%positive
          (Ecast (Eunop Onotbool (Etempvar 96%positive tint) tint) tbool)))
      (Sset 95%positive (Ecast (Etempvar 95%positive tbool) tint)))
    (Sset 95%positive (Econst_int (Int.repr 0) tint)))
  (Sifthenelse (Etempvar 95%positive tint)
    (Sassign
      (Efield
        (Ederef (Etempvar _bn (tptr t_struct_bignum_st)) t_struct_bignum_st)
        _neg tint) (Econst_int (Int.repr 1) tint))
    (Sassign
      (Efield
        (Ederef (Etempvar _bn (tptr t_struct_bignum_st)) t_struct_bignum_st)
        _neg tint) (Econst_int (Int.repr 0) tint))))
|}.

Definition f_bn_correct_top := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr t_struct_bignum_st)) :: nil);
  fn_vars := nil;
  fn_temps := ((_ftl, (tptr tuint)) :: (_tmp_top, tint) ::
               (97%positive, (tptr tuint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _tmp_top
    (Efield
      (Ederef (Etempvar _bn (tptr t_struct_bignum_st)) t_struct_bignum_st)
      _top tint))
  (Sifthenelse (Ebinop Ogt (Etempvar _tmp_top tint)
                 (Econst_int (Int.repr 0) tint) tint)
    (Ssequence
      (Ssequence
        (Sset _ftl
          (Eaddrof
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
                    t_struct_bignum_st) _d (tptr tuint))
                (Ebinop Osub (Etempvar _tmp_top tint)
                  (Econst_int (Int.repr 1) tint) tint) (tptr tuint)) tuint)
            (tptr tuint)))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Ogt (Etempvar _tmp_top tint)
                           (Econst_int (Int.repr 0) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Ssequence
                (Sset 97%positive (Etempvar _ftl (tptr tuint)))
                (Sset _ftl
                  (Ebinop Osub (Etempvar 97%positive (tptr tuint))
                    (Econst_int (Int.repr 1) tint) (tptr tuint))))
              (Sifthenelse (Ederef (Etempvar 97%positive (tptr tuint)) tuint)
                Sbreak
                Sskip)))
          (Sset _tmp_top
            (Ebinop Osub (Etempvar _tmp_top tint)
              (Econst_int (Int.repr 1) tint) tint))))
      (Sassign
        (Efield
          (Ederef (Etempvar _bn (tptr t_struct_bignum_st))
            t_struct_bignum_st) _top tint) (Etempvar _tmp_top tint)))
    Sskip))
|}.

Definition f_bn_expand := {|
  fn_return := (tptr t_struct_bignum_st);
  fn_callconv := cc_default;
  fn_params := ((_bn, (tptr t_struct_bignum_st)) :: (_bits__1, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((98%positive, (tptr t_struct_bignum_st)) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some 98%positive)
    (Evar _bn_wexpand (Tfunction
                        (Tcons (tptr t_struct_bignum_st) (Tcons tuint Tnil))
                        (tptr t_struct_bignum_st) cc_default))
    ((Etempvar _bn (tptr t_struct_bignum_st)) ::
     (Ebinop Odiv
       (Ebinop Osub
         (Ebinop Oadd (Etempvar _bits__1 tuint)
           (Econst_int (Int.repr 32) tint) tuint)
         (Econst_int (Int.repr 1) tint) tuint)
       (Econst_int (Int.repr 32) tint) tuint) :: nil))
  (Sreturn (Some (Etempvar 98%positive (tptr t_struct_bignum_st)))))
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
     tvoid cc_default)) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_memcpy,
   Gfun(External (EF_external _memcpy
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
     (tptr tvoid) cc_default)) ::
 (_memset,
   Gfun(External (EF_external _memset
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil))) (tptr tvoid)
     cc_default)) ::
 (_BN_is_zero,
   Gfun(External (EF_external _BN_is_zero
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr t_struct_bignum_st) Tnil) tint cc_default)) ::
 (_OPENSSL_cleanse,
   Gfun(External (EF_external _OPENSSL_cleanse
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (_mallocN,
   Gfun(External (EF_external _mallocN
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tint Tnil) (tptr tvoid) cc_default)) ::
 (_BN_new, Gfun(Internal f_BN_new)) ::
 (_BN_init, Gfun(Internal f_BN_init)) ::
 (_BN_free, Gfun(Internal f_BN_free)) ::
 (_BN_clear_free, Gfun(Internal f_BN_clear_free)) ::
 (_BN_dup, Gfun(Internal f_BN_dup)) ::
 (_BN_copy, Gfun(Internal f_BN_copy)) ::
 (_BN_clear, Gfun(Internal f_BN_clear)) :: (_data_one, Gvar v_data_one) ::
 (_const_one, Gvar v_const_one) ::
 (_BN_value_one, Gfun(Internal f_BN_value_one)) ::
 (_BN_with_flags, Gfun(Internal f_BN_with_flags)) :: (_bits, Gvar v_bits) ::
 (_BN_num_bits_word, Gfun(Internal f_BN_num_bits_word)) ::
 (_BN_num_bits, Gfun(Internal f_BN_num_bits)) ::
 (_BN_num_bytes, Gfun(Internal f_BN_num_bytes)) ::
 (_BN_zero, Gfun(Internal f_BN_zero)) ::
 (_BN_one, Gfun(Internal f_BN_one)) ::
 (_BN_set_word, Gfun(Internal f_BN_set_word)) ::
 (_BN_is_negative, Gfun(Internal f_BN_is_negative)) ::
 (_bn_wexpand, Gfun(Internal f_bn_wexpand)) ::
 (_BN_set_negative, Gfun(Internal f_BN_set_negative)) ::
 (_bn_correct_top, Gfun(Internal f_bn_correct_top)) ::
 (_bn_expand, Gfun(Internal f_bn_expand)) :: nil);
prog_main := _main
|}.

