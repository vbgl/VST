
Require Import Clightdefs.
Local Open Scope Z_scope.
Definition _ERR_put_error : ident := 72%positive.
Definition _EVP_Digest : ident := 113%positive.
Definition _EVP_DigestFinal : ident := 107%positive.
Definition _EVP_DigestFinal_ex : ident := 106%positive.
Definition _EVP_DigestInit : ident := 100%positive.
Definition _EVP_DigestInit_ex : ident := 99%positive.
Definition _EVP_DigestUpdate : ident := 103%positive.
Definition _EVP_MD_CTX_block_size : ident := 116%positive.
Definition _EVP_MD_CTX_cleanup : ident := 89%positive.
Definition _EVP_MD_CTX_copy : ident := 96%positive.
Definition _EVP_MD_CTX_copy_ex : ident := 95%positive.
Definition _EVP_MD_CTX_create : ident := 88%positive.
Definition _EVP_MD_CTX_destroy : ident := 90%positive.
Definition _EVP_MD_CTX_init : ident := 87%positive.
Definition _EVP_MD_CTX_md : ident := 114%positive.
Definition _EVP_MD_CTX_size : ident := 115%positive.
Definition _EVP_MD_CTX_type : ident := 117%positive.
Definition _EVP_MD_block_size : ident := 85%positive.
Definition _EVP_MD_flags : ident := 83%positive.
Definition _EVP_MD_size : ident := 84%positive.
Definition _EVP_MD_type : ident := 82%positive.
Definition _EVP_add_digest : ident := 118%positive.
Definition _OPENSSL_cleanse : ident := 74%positive.
Definition _OPENSSL_memcpy : ident := 78%positive.
Definition _OPENSSL_memset : ident := 80%positive.
Definition ___builtin_annot : ident := 21%positive.
Definition ___builtin_annot_intval : ident := 22%positive.
Definition ___builtin_bswap : ident := 47%positive.
Definition ___builtin_bswap16 : ident := 50%positive.
Definition ___builtin_bswap32 : ident := 49%positive.
Definition ___builtin_bswap64 : ident := 48%positive.
Definition ___builtin_clz : ident := 51%positive.
Definition ___builtin_clzl : ident := 52%positive.
Definition ___builtin_clzll : ident := 53%positive.
Definition ___builtin_ctz : ident := 54%positive.
Definition ___builtin_ctzl : ident := 55%positive.
Definition ___builtin_ctzll : ident := 56%positive.
Definition ___builtin_debug : ident := 69%positive.
Definition ___builtin_fabs : ident := 19%positive.
Definition ___builtin_fmadd : ident := 60%positive.
Definition ___builtin_fmax : ident := 58%positive.
Definition ___builtin_fmin : ident := 59%positive.
Definition ___builtin_fmsub : ident := 61%positive.
Definition ___builtin_fnmadd : ident := 62%positive.
Definition ___builtin_fnmsub : ident := 63%positive.
Definition ___builtin_fsqrt : ident := 57%positive.
Definition ___builtin_membar : ident := 23%positive.
Definition ___builtin_memcpy_aligned : ident := 20%positive.
Definition ___builtin_nop : ident := 68%positive.
Definition ___builtin_read16_reversed : ident := 64%positive.
Definition ___builtin_read32_reversed : ident := 65%positive.
Definition ___builtin_va_arg : ident := 25%positive.
Definition ___builtin_va_copy : ident := 26%positive.
Definition ___builtin_va_end : ident := 27%positive.
Definition ___builtin_va_start : ident := 24%positive.
Definition ___builtin_write16_reversed : ident := 66%positive.
Definition ___builtin_write32_reversed : ident := 67%positive.
Definition ___compcert_va_composite : ident := 31%positive.
Definition ___compcert_va_float64 : ident := 30%positive.
Definition ___compcert_va_int32 : ident := 28%positive.
Definition ___compcert_va_int64 : ident := 29%positive.
Definition ___i64_dtos : ident := 32%positive.
Definition ___i64_dtou : ident := 33%positive.
Definition ___i64_sar : ident := 44%positive.
Definition ___i64_sdiv : ident := 38%positive.
Definition ___i64_shl : ident := 42%positive.
Definition ___i64_shr : ident := 43%positive.
Definition ___i64_smod : ident := 40%positive.
Definition ___i64_smulh : ident := 45%positive.
Definition ___i64_stod : ident := 34%positive.
Definition ___i64_stof : ident := 36%positive.
Definition ___i64_udiv : ident := 39%positive.
Definition ___i64_umod : ident := 41%positive.
Definition ___i64_umulh : ident := 46%positive.
Definition ___i64_utod : ident := 35%positive.
Definition ___i64_utof : ident := 37%positive.
Definition ___stringlit_1 : ident := 94%positive.
Definition _block_size : ident := 15%positive.
Definition _c : ident := 79%positive.
Definition _count : ident := 108%positive.
Definition _ctx : ident := 86%positive.
Definition _ctx_size : ident := 16%positive.
Definition _data : ident := 101%positive.
Definition _digest : ident := 2%positive.
Definition _dst : ident := 75%positive.
Definition _dup : ident := 18%positive.
Definition _engine : ident := 97%positive.
Definition _engine_st : ident := 98%positive.
Definition _env_md_ctx_st : ident := 8%positive.
Definition _env_md_st : ident := 1%positive.
Definition _evp_md_pctx_ops : ident := 6%positive.
Definition _evp_pkey_ctx_st : ident := 4%positive.
Definition _final : ident := 14%positive.
Definition _flags : ident := 11%positive.
Definition _free : ident := 17%positive.
Definition _impl : ident := 111%positive.
Definition _in : ident := 92%positive.
Definition _init : ident := 12%positive.
Definition _len : ident := 102%positive.
Definition _main : ident := 119%positive.
Definition _malloc : ident := 73%positive.
Definition _md : ident := 81%positive.
Definition _md_data : ident := 3%positive.
Definition _md_out : ident := 104%positive.
Definition _md_size : ident := 10%positive.
Definition _memcpy : ident := 70%positive.
Definition _memset : ident := 71%positive.
Definition _n : ident := 77%positive.
Definition _out : ident := 91%positive.
Definition _out_md : ident := 109%positive.
Definition _out_size : ident := 110%positive.
Definition _pctx : ident := 5%positive.
Definition _pctx_ops : ident := 7%positive.
Definition _ret : ident := 112%positive.
Definition _size : ident := 105%positive.
Definition _src : ident := 76%positive.
Definition _tmp_buf : ident := 93%positive.
Definition _type : ident := 9%positive.
Definition _update : ident := 13%positive.
Definition _t'1 : ident := 120%positive.
Definition _t'10 : ident := 129%positive.
Definition _t'11 : ident := 130%positive.
Definition _t'12 : ident := 131%positive.
Definition _t'13 : ident := 132%positive.
Definition _t'14 : ident := 133%positive.
Definition _t'15 : ident := 134%positive.
Definition _t'16 : ident := 135%positive.
Definition _t'17 : ident := 136%positive.
Definition _t'18 : ident := 137%positive.
Definition _t'19 : ident := 138%positive.
Definition _t'2 : ident := 121%positive.
Definition _t'20 : ident := 139%positive.
Definition _t'21 : ident := 140%positive.
Definition _t'22 : ident := 141%positive.
Definition _t'23 : ident := 142%positive.
Definition _t'24 : ident := 143%positive.
Definition _t'25 : ident := 144%positive.
Definition _t'26 : ident := 145%positive.
Definition _t'3 : ident := 122%positive.
Definition _t'4 : ident := 123%positive.
Definition _t'5 : ident := 124%positive.
Definition _t'6 : ident := 125%positive.
Definition _t'7 : ident := 126%positive.
Definition _t'8 : ident := 127%positive.
Definition _t'9 : ident := 128%positive.

Definition v___stringlit_1 := {|
  gvar_info := (tarray tschar 9);
  gvar_init := (Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 103) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 115) :: Init_int8 (Int.repr 116) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 0) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_OPENSSL_memcpy := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr tvoid)) :: (_src, (tptr tvoid)) ::
                (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _n tuint) (Econst_int (Int.repr 0) tint)
                 tint)
    (Sreturn (Some (Etempvar _dst (tptr tvoid))))
    Sskip)
  (Ssequence
    (Scall (Some _t'1)
      (Evar _memcpy (Tfunction
                      (Tcons (tptr tvoid)
                        (Tcons (tptr tvoid) (Tcons tuint Tnil))) (tptr tvoid)
                      cc_default))
      ((Etempvar _dst (tptr tvoid)) :: (Etempvar _src (tptr tvoid)) ::
       (Etempvar _n tuint) :: nil))
    (Sreturn (Some (Etempvar _t'1 (tptr tvoid))))))
|}.

Definition f_OPENSSL_memset := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr tvoid)) :: (_c, tint) :: (_n, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq (Etempvar _n tuint) (Econst_int (Int.repr 0) tint)
                 tint)
    (Sreturn (Some (Etempvar _dst (tptr tvoid))))
    Sskip)
  (Ssequence
    (Scall (Some _t'1)
      (Evar _memset (Tfunction
                      (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil)))
                      (tptr tvoid) cc_default))
      ((Etempvar _dst (tptr tvoid)) :: (Etempvar _c tint) ::
       (Etempvar _n tuint) :: nil))
    (Sreturn (Some (Etempvar _t'1 (tptr tvoid))))))
|}.

Definition f_EVP_MD_type := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_md, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _md (tptr (Tstruct _env_md_st noattr)))
        (Tstruct _env_md_st noattr)) _type tint))
  (Sreturn (Some (Etempvar _t'1 tint))))
|}.

Definition f_EVP_MD_flags := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_md, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _md (tptr (Tstruct _env_md_st noattr)))
        (Tstruct _env_md_st noattr)) _flags tuint))
  (Sreturn (Some (Etempvar _t'1 tuint))))
|}.

Definition f_EVP_MD_size := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_md, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _md (tptr (Tstruct _env_md_st noattr)))
        (Tstruct _env_md_st noattr)) _md_size tuint))
  (Sreturn (Some (Etempvar _t'1 tuint))))
|}.

Definition f_EVP_MD_block_size := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_md, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _md (tptr (Tstruct _env_md_st noattr)))
        (Tstruct _env_md_st noattr)) _block_size tuint))
  (Sreturn (Some (Etempvar _t'1 tuint))))
|}.

Definition f_EVP_MD_CTX_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _OPENSSL_memset (Tfunction
                          (Tcons (tptr tvoid)
                            (Tcons tint (Tcons tuint Tnil))) (tptr tvoid)
                          cc_default))
  ((Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr))) ::
   (Econst_int (Int.repr 0) tint) ::
   (Esizeof (Tstruct _env_md_ctx_st noattr) tuint) :: nil))
|}.

Definition f_EVP_MD_CTX_create := {|
  fn_return := (tptr (Tstruct _env_md_ctx_st noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tuint Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _env_md_ctx_st noattr) tuint) :: nil))
    (Sset _ctx (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
      (Scall None
        (Evar _EVP_MD_CTX_init (Tfunction
                                 (Tcons
                                   (tptr (Tstruct _env_md_ctx_st noattr))
                                   Tnil) tvoid cc_default))
        ((Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr))) :: nil))
      Sskip)
    (Sreturn (Some (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))))))
|}.

Definition f_EVP_MD_CTX_cleanup := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tint) :: (_t'14, tuint) ::
               (_t'13, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'12, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'11, (tptr tvoid)) :: (_t'10, tuint) ::
               (_t'9, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'8, (tptr tvoid)) :: (_t'7, (tptr tvoid)) ::
               (_t'6, (tptr (Tstruct _evp_pkey_ctx_st noattr))) ::
               (_t'5,
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _evp_pkey_ctx_st noattr)) Tnil)
                        tvoid cc_default))) ::
               (_t'4, (tptr (Tstruct _evp_md_pctx_ops noattr))) ::
               (_t'3, (tptr (Tstruct _evp_md_pctx_ops noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'12
          (Efield
            (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
              (Tstruct _env_md_ctx_st noattr)) _digest
            (tptr (Tstruct _env_md_st noattr))))
        (Sifthenelse (Etempvar _t'12 (tptr (Tstruct _env_md_st noattr)))
          (Ssequence
            (Sset _t'13
              (Efield
                (Ederef
                  (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
                  (Tstruct _env_md_ctx_st noattr)) _digest
                (tptr (Tstruct _env_md_st noattr))))
            (Ssequence
              (Sset _t'14
                (Efield
                  (Ederef (Etempvar _t'13 (tptr (Tstruct _env_md_st noattr)))
                    (Tstruct _env_md_st noattr)) _ctx_size tuint))
              (Sset _t'1 (Ecast (Etempvar _t'14 tuint) tbool))))
          (Sset _t'1 (Econst_int (Int.repr 0) tint))))
      (Sifthenelse (Etempvar _t'1 tint)
        (Ssequence
          (Sset _t'11
            (Efield
              (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
                (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
          (Sset _t'2 (Ecast (Etempvar _t'11 (tptr tvoid)) tbool)))
        (Sset _t'2 (Econst_int (Int.repr 0) tint))))
    (Sifthenelse (Etempvar _t'2 tint)
      (Ssequence
        (Ssequence
          (Sset _t'8
            (Efield
              (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
                (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
          (Ssequence
            (Sset _t'9
              (Efield
                (Ederef
                  (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
                  (Tstruct _env_md_ctx_st noattr)) _digest
                (tptr (Tstruct _env_md_st noattr))))
            (Ssequence
              (Sset _t'10
                (Efield
                  (Ederef (Etempvar _t'9 (tptr (Tstruct _env_md_st noattr)))
                    (Tstruct _env_md_st noattr)) _ctx_size tuint))
              (Scall None
                (Evar _OPENSSL_cleanse (Tfunction
                                         (Tcons (tptr tvoid)
                                           (Tcons tuint Tnil)) tvoid
                                         cc_default))
                ((Etempvar _t'8 (tptr tvoid)) :: (Etempvar _t'10 tuint) ::
                 nil)))))
        (Ssequence
          (Sset _t'7
            (Efield
              (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
                (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
          (Scall None
            (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                          cc_default)) ((Etempvar _t'7 (tptr tvoid)) :: nil))))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
            (Tstruct _env_md_ctx_st noattr)) _pctx_ops
          (tptr (Tstruct _evp_md_pctx_ops noattr))))
      (Sifthenelse (Etempvar _t'3 (tptr (Tstruct _evp_md_pctx_ops noattr)))
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
                (Tstruct _env_md_ctx_st noattr)) _pctx_ops
              (tptr (Tstruct _evp_md_pctx_ops noattr))))
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef
                  (Etempvar _t'4 (tptr (Tstruct _evp_md_pctx_ops noattr)))
                  (Tstruct _evp_md_pctx_ops noattr)) _free
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _evp_pkey_ctx_st noattr)) Tnil)
                        tvoid cc_default))))
            (Ssequence
              (Sset _t'6
                (Efield
                  (Ederef
                    (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
                    (Tstruct _env_md_ctx_st noattr)) _pctx
                  (tptr (Tstruct _evp_pkey_ctx_st noattr))))
              (Scall None
                (Etempvar _t'5 (tptr (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _evp_pkey_ctx_st noattr))
                                         Tnil) tvoid cc_default)))
                ((Etempvar _t'6 (tptr (Tstruct _evp_pkey_ctx_st noattr))) ::
                 nil)))))
        Sskip))
    (Ssequence
      (Scall None
        (Evar _EVP_MD_CTX_init (Tfunction
                                 (Tcons
                                   (tptr (Tstruct _env_md_ctx_st noattr))
                                   Tnil) tvoid cc_default))
        ((Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr))) :: nil))
      (Sreturn (Some (Econst_int (Int.repr 1) tint))))))
|}.

Definition f_EVP_MD_CTX_destroy := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Eunop Onotbool
                 (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr))) tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Scall None
      (Evar _EVP_MD_CTX_cleanup (Tfunction
                                  (Tcons
                                    (tptr (Tstruct _env_md_ctx_st noattr))
                                    Tnil) tint cc_default))
      ((Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr))) :: nil))
    (Scall None
      (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default))
      ((Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr))) :: nil))))
|}.

Definition f_EVP_MD_CTX_copy_ex := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_in, (tptr (Tstruct _env_md_ctx_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_tmp_buf, (tptr tuchar)) :: (_t'5, tint) ::
               (_t'4, (tptr (Tstruct _evp_pkey_ctx_st noattr))) ::
               (_t'3, tint) :: (_t'2, (tptr tvoid)) :: (_t'1, tint) ::
               (_t'26, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'25, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'24, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'23, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'22, tuint) ::
               (_t'21, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'20, (tptr tvoid)) :: (_t'19, tuint) ::
               (_t'18, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'17, (tptr tvoid)) :: (_t'16, tuint) ::
               (_t'15, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'14, (tptr tvoid)) :: (_t'13, (tptr tvoid)) ::
               (_t'12, (tptr (Tstruct _evp_md_pctx_ops noattr))) ::
               (_t'11, (tptr (Tstruct _evp_md_pctx_ops noattr))) ::
               (_t'10, (tptr (Tstruct _evp_pkey_ctx_st noattr))) ::
               (_t'9, (tptr (Tstruct _evp_pkey_ctx_st noattr))) ::
               (_t'8,
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _evp_pkey_ctx_st noattr)) Tnil)
                        (tptr (Tstruct _evp_pkey_ctx_st noattr)) cc_default))) ::
               (_t'7, (tptr (Tstruct _evp_md_pctx_ops noattr))) ::
               (_t'6, (tptr (Tstruct _evp_pkey_ctx_st noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _tmp_buf (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Ssequence
      (Sifthenelse (Ebinop Oeq
                     (Etempvar _in (tptr (Tstruct _env_md_ctx_st noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sset _t'1 (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Sset _t'26
            (Efield
              (Ederef (Etempvar _in (tptr (Tstruct _env_md_ctx_st noattr)))
                (Tstruct _env_md_ctx_st noattr)) _digest
              (tptr (Tstruct _env_md_st noattr))))
          (Sset _t'1
            (Ecast
              (Ebinop Oeq (Etempvar _t'26 (tptr (Tstruct _env_md_st noattr)))
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
              tbool))))
      (Sifthenelse (Etempvar _t'1 tint)
        (Ssequence
          (Scall None
            (Evar _ERR_put_error (Tfunction
                                   (Tcons tint
                                     (Tcons tint
                                       (Tcons tint
                                         (Tcons (tptr tschar)
                                           (Tcons tuint Tnil))))) tvoid
                                   cc_default))
            ((Econst_int (Int.repr 29) tint) ::
             (Econst_int (Int.repr 0) tint) ::
             (Econst_int (Int.repr 100) tint) ::
             (Evar ___stringlit_1 (tarray tschar 9)) ::
             (Econst_int (Int.repr 121) tint) :: nil))
          (Sreturn (Some (Econst_int (Int.repr 0) tint))))
        Sskip))
    (Ssequence
      (Ssequence
        (Sset _t'24
          (Efield
            (Ederef (Etempvar _out (tptr (Tstruct _env_md_ctx_st noattr)))
              (Tstruct _env_md_ctx_st noattr)) _digest
            (tptr (Tstruct _env_md_st noattr))))
        (Ssequence
          (Sset _t'25
            (Efield
              (Ederef (Etempvar _in (tptr (Tstruct _env_md_ctx_st noattr)))
                (Tstruct _env_md_ctx_st noattr)) _digest
              (tptr (Tstruct _env_md_st noattr))))
          (Sifthenelse (Ebinop Oeq
                         (Etempvar _t'24 (tptr (Tstruct _env_md_st noattr)))
                         (Etempvar _t'25 (tptr (Tstruct _env_md_st noattr)))
                         tint)
            (Ssequence
              (Sset _tmp_buf
                (Efield
                  (Ederef
                    (Etempvar _out (tptr (Tstruct _env_md_ctx_st noattr)))
                    (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _out (tptr (Tstruct _env_md_ctx_st noattr)))
                    (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid))
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
            Sskip)))
      (Ssequence
        (Scall None
          (Evar _EVP_MD_CTX_cleanup (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _env_md_ctx_st noattr))
                                        Tnil) tint cc_default))
          ((Etempvar _out (tptr (Tstruct _env_md_ctx_st noattr))) :: nil))
        (Ssequence
          (Ssequence
            (Sset _t'23
              (Efield
                (Ederef (Etempvar _in (tptr (Tstruct _env_md_ctx_st noattr)))
                  (Tstruct _env_md_ctx_st noattr)) _digest
                (tptr (Tstruct _env_md_st noattr))))
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _out (tptr (Tstruct _env_md_ctx_st noattr)))
                  (Tstruct _env_md_ctx_st noattr)) _digest
                (tptr (Tstruct _env_md_st noattr)))
              (Etempvar _t'23 (tptr (Tstruct _env_md_st noattr)))))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'20
                  (Efield
                    (Ederef
                      (Etempvar _in (tptr (Tstruct _env_md_ctx_st noattr)))
                      (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
                (Sifthenelse (Etempvar _t'20 (tptr tvoid))
                  (Ssequence
                    (Sset _t'21
                      (Efield
                        (Ederef
                          (Etempvar _in (tptr (Tstruct _env_md_ctx_st noattr)))
                          (Tstruct _env_md_ctx_st noattr)) _digest
                        (tptr (Tstruct _env_md_st noattr))))
                    (Ssequence
                      (Sset _t'22
                        (Efield
                          (Ederef
                            (Etempvar _t'21 (tptr (Tstruct _env_md_st noattr)))
                            (Tstruct _env_md_st noattr)) _ctx_size tuint))
                      (Sset _t'3 (Ecast (Etempvar _t'22 tuint) tbool))))
                  (Sset _t'3 (Econst_int (Int.repr 0) tint))))
              (Sifthenelse (Etempvar _t'3 tint)
                (Ssequence
                  (Sifthenelse (Etempvar _tmp_buf (tptr tuchar))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _out (tptr (Tstruct _env_md_ctx_st noattr)))
                          (Tstruct _env_md_ctx_st noattr)) _md_data
                        (tptr tvoid)) (Etempvar _tmp_buf (tptr tuchar)))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'18
                            (Efield
                              (Ederef
                                (Etempvar _in (tptr (Tstruct _env_md_ctx_st noattr)))
                                (Tstruct _env_md_ctx_st noattr)) _digest
                              (tptr (Tstruct _env_md_st noattr))))
                          (Ssequence
                            (Sset _t'19
                              (Efield
                                (Ederef
                                  (Etempvar _t'18 (tptr (Tstruct _env_md_st noattr)))
                                  (Tstruct _env_md_st noattr)) _ctx_size
                                tuint))
                            (Scall (Some _t'2)
                              (Evar _malloc (Tfunction (Tcons tuint Tnil)
                                              (tptr tvoid) cc_default))
                              ((Etempvar _t'19 tuint) :: nil))))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _out (tptr (Tstruct _env_md_ctx_st noattr)))
                              (Tstruct _env_md_ctx_st noattr)) _md_data
                            (tptr tvoid)) (Etempvar _t'2 (tptr tvoid))))
                      (Ssequence
                        (Sset _t'17
                          (Efield
                            (Ederef
                              (Etempvar _out (tptr (Tstruct _env_md_ctx_st noattr)))
                              (Tstruct _env_md_ctx_st noattr)) _md_data
                            (tptr tvoid)))
                        (Sifthenelse (Eunop Onotbool
                                       (Etempvar _t'17 (tptr tvoid)) tint)
                          (Ssequence
                            (Scall None
                              (Evar _ERR_put_error (Tfunction
                                                     (Tcons tint
                                                       (Tcons tint
                                                         (Tcons tint
                                                           (Tcons
                                                             (tptr tschar)
                                                             (Tcons tuint
                                                               Tnil)))))
                                                     tvoid cc_default))
                              ((Econst_int (Int.repr 29) tint) ::
                               (Econst_int (Int.repr 0) tint) ::
                               (Ebinop Oor (Econst_int (Int.repr 1) tint)
                                 (Econst_int (Int.repr 64) tint) tint) ::
                               (Evar ___stringlit_1 (tarray tschar 9)) ::
                               (Econst_int (Int.repr 142) tint) :: nil))
                            (Sreturn (Some (Econst_int (Int.repr 0) tint))))
                          Sskip))))
                  (Ssequence
                    (Sset _t'13
                      (Efield
                        (Ederef
                          (Etempvar _out (tptr (Tstruct _env_md_ctx_st noattr)))
                          (Tstruct _env_md_ctx_st noattr)) _md_data
                        (tptr tvoid)))
                    (Ssequence
                      (Sset _t'14
                        (Efield
                          (Ederef
                            (Etempvar _in (tptr (Tstruct _env_md_ctx_st noattr)))
                            (Tstruct _env_md_ctx_st noattr)) _md_data
                          (tptr tvoid)))
                      (Ssequence
                        (Sset _t'15
                          (Efield
                            (Ederef
                              (Etempvar _in (tptr (Tstruct _env_md_ctx_st noattr)))
                              (Tstruct _env_md_ctx_st noattr)) _digest
                            (tptr (Tstruct _env_md_st noattr))))
                        (Ssequence
                          (Sset _t'16
                            (Efield
                              (Ederef
                                (Etempvar _t'15 (tptr (Tstruct _env_md_st noattr)))
                                (Tstruct _env_md_st noattr)) _ctx_size tuint))
                          (Scall None
                            (Evar _OPENSSL_memcpy (Tfunction
                                                    (Tcons (tptr tvoid)
                                                      (Tcons (tptr tvoid)
                                                        (Tcons tuint Tnil)))
                                                    (tptr tvoid) cc_default))
                            ((Etempvar _t'13 (tptr tvoid)) ::
                             (Etempvar _t'14 (tptr tvoid)) ::
                             (Etempvar _t'16 tuint) :: nil)))))))
                Sskip))
            (Ssequence
              (Ssequence
                (Sset _t'12
                  (Efield
                    (Ederef
                      (Etempvar _in (tptr (Tstruct _env_md_ctx_st noattr)))
                      (Tstruct _env_md_ctx_st noattr)) _pctx_ops
                    (tptr (Tstruct _evp_md_pctx_ops noattr))))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _out (tptr (Tstruct _env_md_ctx_st noattr)))
                      (Tstruct _env_md_ctx_st noattr)) _pctx_ops
                    (tptr (Tstruct _evp_md_pctx_ops noattr)))
                  (Etempvar _t'12 (tptr (Tstruct _evp_md_pctx_ops noattr)))))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'10
                      (Efield
                        (Ederef
                          (Etempvar _in (tptr (Tstruct _env_md_ctx_st noattr)))
                          (Tstruct _env_md_ctx_st noattr)) _pctx
                        (tptr (Tstruct _evp_pkey_ctx_st noattr))))
                    (Sifthenelse (Etempvar _t'10 (tptr (Tstruct _evp_pkey_ctx_st noattr)))
                      (Ssequence
                        (Sset _t'11
                          (Efield
                            (Ederef
                              (Etempvar _in (tptr (Tstruct _env_md_ctx_st noattr)))
                              (Tstruct _env_md_ctx_st noattr)) _pctx_ops
                            (tptr (Tstruct _evp_md_pctx_ops noattr))))
                        (Sset _t'5
                          (Ecast
                            (Etempvar _t'11 (tptr (Tstruct _evp_md_pctx_ops noattr)))
                            tbool)))
                      (Sset _t'5 (Econst_int (Int.repr 0) tint))))
                  (Sifthenelse (Etempvar _t'5 tint)
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'7
                            (Efield
                              (Ederef
                                (Etempvar _in (tptr (Tstruct _env_md_ctx_st noattr)))
                                (Tstruct _env_md_ctx_st noattr)) _pctx_ops
                              (tptr (Tstruct _evp_md_pctx_ops noattr))))
                          (Ssequence
                            (Sset _t'8
                              (Efield
                                (Ederef
                                  (Etempvar _t'7 (tptr (Tstruct _evp_md_pctx_ops noattr)))
                                  (Tstruct _evp_md_pctx_ops noattr)) _dup
                                (tptr (Tfunction
                                        (Tcons
                                          (tptr (Tstruct _evp_pkey_ctx_st noattr))
                                          Tnil)
                                        (tptr (Tstruct _evp_pkey_ctx_st noattr))
                                        cc_default))))
                            (Ssequence
                              (Sset _t'9
                                (Efield
                                  (Ederef
                                    (Etempvar _in (tptr (Tstruct _env_md_ctx_st noattr)))
                                    (Tstruct _env_md_ctx_st noattr)) _pctx
                                  (tptr (Tstruct _evp_pkey_ctx_st noattr))))
                              (Scall (Some _t'4)
                                (Etempvar _t'8 (tptr (Tfunction
                                                       (Tcons
                                                         (tptr (Tstruct _evp_pkey_ctx_st noattr))
                                                         Tnil)
                                                       (tptr (Tstruct _evp_pkey_ctx_st noattr))
                                                       cc_default)))
                                ((Etempvar _t'9 (tptr (Tstruct _evp_pkey_ctx_st noattr))) ::
                                 nil)))))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _out (tptr (Tstruct _env_md_ctx_st noattr)))
                              (Tstruct _env_md_ctx_st noattr)) _pctx
                            (tptr (Tstruct _evp_pkey_ctx_st noattr)))
                          (Etempvar _t'4 (tptr (Tstruct _evp_pkey_ctx_st noattr)))))
                      (Ssequence
                        (Sset _t'6
                          (Efield
                            (Ederef
                              (Etempvar _out (tptr (Tstruct _env_md_ctx_st noattr)))
                              (Tstruct _env_md_ctx_st noattr)) _pctx
                            (tptr (Tstruct _evp_pkey_ctx_st noattr))))
                        (Sifthenelse (Eunop Onotbool
                                       (Etempvar _t'6 (tptr (Tstruct _evp_pkey_ctx_st noattr)))
                                       tint)
                          (Ssequence
                            (Scall None
                              (Evar _EVP_MD_CTX_cleanup (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _env_md_ctx_st noattr))
                                                            Tnil) tint
                                                          cc_default))
                              ((Etempvar _out (tptr (Tstruct _env_md_ctx_st noattr))) ::
                               nil))
                            (Sreturn (Some (Econst_int (Int.repr 0) tint))))
                          Sskip)))
                    Sskip))
                (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))))))
|}.

Definition f_EVP_MD_CTX_copy := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_in, (tptr (Tstruct _env_md_ctx_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _EVP_MD_CTX_init (Tfunction
                             (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                               Tnil) tvoid cc_default))
    ((Etempvar _out (tptr (Tstruct _env_md_ctx_st noattr))) :: nil))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _EVP_MD_CTX_copy_ex (Tfunction
                                  (Tcons
                                    (tptr (Tstruct _env_md_ctx_st noattr))
                                    (Tcons
                                      (tptr (Tstruct _env_md_ctx_st noattr))
                                      Tnil)) tint cc_default))
      ((Etempvar _out (tptr (Tstruct _env_md_ctx_st noattr))) ::
       (Etempvar _in (tptr (Tstruct _env_md_ctx_st noattr))) :: nil))
    (Sreturn (Some (Etempvar _t'1 tint)))))
|}.

Definition f_EVP_DigestInit_ex := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_type, (tptr (Tstruct _env_md_st noattr))) ::
                (_engine, (tptr (Tstruct _engine_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr tvoid)) :: (_t'1, tint) :: (_t'12, tuint) ::
               (_t'11, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'10, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'9, (tptr tvoid)) :: (_t'8, tuint) ::
               (_t'7, (tptr tvoid)) :: (_t'6, tuint) ::
               (_t'5, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'4,
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _env_md_ctx_st noattr)) Tnil)
                        tvoid cc_default))) ::
               (_t'3, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'5
      (Efield
        (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
          (Tstruct _env_md_ctx_st noattr)) _digest
        (tptr (Tstruct _env_md_st noattr))))
    (Sifthenelse (Ebinop One
                   (Etempvar _t'5 (tptr (Tstruct _env_md_st noattr)))
                   (Etempvar _type (tptr (Tstruct _env_md_st noattr))) tint)
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'10
              (Efield
                (Ederef
                  (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
                  (Tstruct _env_md_ctx_st noattr)) _digest
                (tptr (Tstruct _env_md_st noattr))))
            (Sifthenelse (Etempvar _t'10 (tptr (Tstruct _env_md_st noattr)))
              (Ssequence
                (Sset _t'11
                  (Efield
                    (Ederef
                      (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
                      (Tstruct _env_md_ctx_st noattr)) _digest
                    (tptr (Tstruct _env_md_st noattr))))
                (Ssequence
                  (Sset _t'12
                    (Efield
                      (Ederef
                        (Etempvar _t'11 (tptr (Tstruct _env_md_st noattr)))
                        (Tstruct _env_md_st noattr)) _ctx_size tuint))
                  (Sset _t'1
                    (Ecast
                      (Ebinop Ogt (Etempvar _t'12 tuint)
                        (Econst_int (Int.repr 0) tint) tint) tbool))))
              (Sset _t'1 (Econst_int (Int.repr 0) tint))))
          (Sifthenelse (Etempvar _t'1 tint)
            (Ssequence
              (Ssequence
                (Sset _t'9
                  (Efield
                    (Ederef
                      (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
                      (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
                (Scall None
                  (Evar _free (Tfunction (Tcons (tptr tvoid) Tnil) tvoid
                                cc_default))
                  ((Etempvar _t'9 (tptr tvoid)) :: nil)))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
                    (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid))
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
            Sskip))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
                (Tstruct _env_md_ctx_st noattr)) _digest
              (tptr (Tstruct _env_md_st noattr)))
            (Etempvar _type (tptr (Tstruct _env_md_st noattr))))
          (Ssequence
            (Sset _t'6
              (Efield
                (Ederef (Etempvar _type (tptr (Tstruct _env_md_st noattr)))
                  (Tstruct _env_md_st noattr)) _ctx_size tuint))
            (Sifthenelse (Ebinop Ogt (Etempvar _t'6 tuint)
                           (Econst_int (Int.repr 0) tint) tint)
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'8
                      (Efield
                        (Ederef
                          (Etempvar _type (tptr (Tstruct _env_md_st noattr)))
                          (Tstruct _env_md_st noattr)) _ctx_size tuint))
                    (Scall (Some _t'2)
                      (Evar _malloc (Tfunction (Tcons tuint Tnil)
                                      (tptr tvoid) cc_default))
                      ((Etempvar _t'8 tuint) :: nil)))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
                        (Tstruct _env_md_ctx_st noattr)) _md_data
                      (tptr tvoid)) (Etempvar _t'2 (tptr tvoid))))
                (Ssequence
                  (Sset _t'7
                    (Efield
                      (Ederef
                        (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
                        (Tstruct _env_md_ctx_st noattr)) _md_data
                      (tptr tvoid)))
                  (Sifthenelse (Ebinop Oeq (Etempvar _t'7 (tptr tvoid))
                                 (Ecast (Econst_int (Int.repr 0) tint)
                                   (tptr tvoid)) tint)
                    (Ssequence
                      (Scall None
                        (Evar _ERR_put_error (Tfunction
                                               (Tcons tint
                                                 (Tcons tint
                                                   (Tcons tint
                                                     (Tcons (tptr tschar)
                                                       (Tcons tuint Tnil)))))
                                               tvoid cc_default))
                        ((Econst_int (Int.repr 29) tint) ::
                         (Econst_int (Int.repr 0) tint) ::
                         (Ebinop Oor (Econst_int (Int.repr 1) tint)
                           (Econst_int (Int.repr 64) tint) tint) ::
                         (Evar ___stringlit_1 (tarray tschar 9)) ::
                         (Econst_int (Int.repr 177) tint) :: nil))
                      (Sreturn (Some (Econst_int (Int.repr 0) tint))))
                    Sskip)))
              Sskip))))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
            (Tstruct _env_md_ctx_st noattr)) _digest
          (tptr (Tstruct _env_md_st noattr))))
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _t'3 (tptr (Tstruct _env_md_st noattr)))
              (Tstruct _env_md_st noattr)) _init
            (tptr (Tfunction
                    (Tcons (tptr (Tstruct _env_md_ctx_st noattr)) Tnil) tvoid
                    cc_default))))
        (Scall None
          (Etempvar _t'4 (tptr (Tfunction
                                 (Tcons
                                   (tptr (Tstruct _env_md_ctx_st noattr))
                                   Tnil) tvoid cc_default)))
          ((Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr))) :: nil))))
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))))
|}.

Definition f_EVP_DigestInit := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_type, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _EVP_MD_CTX_init (Tfunction
                             (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                               Tnil) tvoid cc_default))
    ((Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr))) :: nil))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _EVP_DigestInit_ex (Tfunction
                                 (Tcons
                                   (tptr (Tstruct _env_md_ctx_st noattr))
                                   (Tcons (tptr (Tstruct _env_md_st noattr))
                                     (Tcons
                                       (tptr (Tstruct _engine_st noattr))
                                       Tnil))) tint cc_default))
      ((Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr))) ::
       (Etempvar _type (tptr (Tstruct _env_md_st noattr))) ::
       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) :: nil))
    (Sreturn (Some (Etempvar _t'1 tint)))))
|}.

Definition f_EVP_DigestUpdate := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_data, (tptr tvoid)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2,
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                          (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                        cc_default))) ::
               (_t'1, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
          (Tstruct _env_md_ctx_st noattr)) _digest
        (tptr (Tstruct _env_md_st noattr))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _t'1 (tptr (Tstruct _env_md_st noattr)))
            (Tstruct _env_md_st noattr)) _update
          (tptr (Tfunction
                  (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                    (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                  cc_default))))
      (Scall None
        (Etempvar _t'2 (tptr (Tfunction
                               (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                                 (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                               tvoid cc_default)))
        ((Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr))) ::
         (Etempvar _data (tptr tvoid)) :: (Etempvar _len tuint) :: nil))))
  (Sreturn (Some (Econst_int (Int.repr 1) tint))))
|}.

Definition f_EVP_DigestFinal_ex := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_md_out, (tptr tuchar)) :: (_size, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'7,
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                          (Tcons (tptr tuchar) Tnil)) tvoid cc_default))) ::
               (_t'6, (tptr (Tstruct _env_md_st noattr))) :: (_t'5, tuint) ::
               (_t'4, (tptr (Tstruct _env_md_st noattr))) :: (_t'3, tuint) ::
               (_t'2, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'1, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'6
      (Efield
        (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
          (Tstruct _env_md_ctx_st noattr)) _digest
        (tptr (Tstruct _env_md_st noattr))))
    (Ssequence
      (Sset _t'7
        (Efield
          (Ederef (Etempvar _t'6 (tptr (Tstruct _env_md_st noattr)))
            (Tstruct _env_md_st noattr)) _final
          (tptr (Tfunction
                  (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                    (Tcons (tptr tuchar) Tnil)) tvoid cc_default))))
      (Scall None
        (Etempvar _t'7 (tptr (Tfunction
                               (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                                 (Tcons (tptr tuchar) Tnil)) tvoid
                               cc_default)))
        ((Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr))) ::
         (Etempvar _md_out (tptr tuchar)) :: nil))))
  (Ssequence
    (Sifthenelse (Ebinop One (Etempvar _size (tptr tuint))
                   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
              (Tstruct _env_md_ctx_st noattr)) _digest
            (tptr (Tstruct _env_md_st noattr))))
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _t'4 (tptr (Tstruct _env_md_st noattr)))
                (Tstruct _env_md_st noattr)) _md_size tuint))
          (Sassign (Ederef (Etempvar _size (tptr tuint)) tuint)
            (Etempvar _t'5 tuint))))
      Sskip)
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
              (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
                (Tstruct _env_md_ctx_st noattr)) _digest
              (tptr (Tstruct _env_md_st noattr))))
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef (Etempvar _t'2 (tptr (Tstruct _env_md_st noattr)))
                  (Tstruct _env_md_st noattr)) _ctx_size tuint))
            (Scall None
              (Evar _OPENSSL_cleanse (Tfunction
                                       (Tcons (tptr tvoid)
                                         (Tcons tuint Tnil)) tvoid
                                       cc_default))
              ((Etempvar _t'1 (tptr tvoid)) :: (Etempvar _t'3 tuint) :: nil)))))
      (Sreturn (Some (Econst_int (Int.repr 1) tint))))))
|}.

Definition f_EVP_DigestFinal := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_md, (tptr tuchar)) :: (_size, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _EVP_DigestFinal_ex (Tfunction
                                (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                                  (Tcons (tptr tuchar)
                                    (Tcons (tptr tuint) Tnil))) tint
                                cc_default))
    ((Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr))) ::
     (Etempvar _md (tptr tuchar)) :: (Etempvar _size (tptr tuint)) :: nil))
  (Ssequence
    (Scall None
      (Evar _EVP_MD_CTX_cleanup (Tfunction
                                  (Tcons
                                    (tptr (Tstruct _env_md_ctx_st noattr))
                                    Tnil) tint cc_default))
      ((Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr))) :: nil))
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))))
|}.

Definition f_EVP_Digest := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_data, (tptr tvoid)) :: (_count, tuint) ::
                (_out_md, (tptr tuchar)) :: (_out_size, (tptr tuint)) ::
                (_type, (tptr (Tstruct _env_md_st noattr))) ::
                (_impl, (tptr (Tstruct _engine_st noattr))) :: nil);
  fn_vars := ((_ctx, (Tstruct _env_md_ctx_st noattr)) :: nil);
  fn_temps := ((_ret, tint) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _EVP_MD_CTX_init (Tfunction
                             (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                               Tnil) tvoid cc_default))
    ((Eaddrof (Evar _ctx (Tstruct _env_md_ctx_st noattr))
       (tptr (Tstruct _env_md_ctx_st noattr))) :: nil))
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _EVP_DigestInit_ex (Tfunction
                                       (Tcons
                                         (tptr (Tstruct _env_md_ctx_st noattr))
                                         (Tcons
                                           (tptr (Tstruct _env_md_st noattr))
                                           (Tcons
                                             (tptr (Tstruct _engine_st noattr))
                                             Tnil))) tint cc_default))
            ((Eaddrof (Evar _ctx (Tstruct _env_md_ctx_st noattr))
               (tptr (Tstruct _env_md_ctx_st noattr))) ::
             (Etempvar _type (tptr (Tstruct _env_md_st noattr))) ::
             (Etempvar _impl (tptr (Tstruct _engine_st noattr))) :: nil))
          (Sifthenelse (Etempvar _t'1 tint)
            (Ssequence
              (Scall (Some _t'3)
                (Evar _EVP_DigestUpdate (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _env_md_ctx_st noattr))
                                            (Tcons (tptr tvoid)
                                              (Tcons tuint Tnil))) tint
                                          cc_default))
                ((Eaddrof (Evar _ctx (Tstruct _env_md_ctx_st noattr))
                   (tptr (Tstruct _env_md_ctx_st noattr))) ::
                 (Etempvar _data (tptr tvoid)) :: (Etempvar _count tuint) ::
                 nil))
              (Sset _t'2 (Ecast (Etempvar _t'3 tint) tbool)))
            (Sset _t'2 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'2 tint)
          (Ssequence
            (Scall (Some _t'5)
              (Evar _EVP_DigestFinal_ex (Tfunction
                                          (Tcons
                                            (tptr (Tstruct _env_md_ctx_st noattr))
                                            (Tcons (tptr tuchar)
                                              (Tcons (tptr tuint) Tnil)))
                                          tint cc_default))
              ((Eaddrof (Evar _ctx (Tstruct _env_md_ctx_st noattr))
                 (tptr (Tstruct _env_md_ctx_st noattr))) ::
               (Etempvar _out_md (tptr tuchar)) ::
               (Etempvar _out_size (tptr tuint)) :: nil))
            (Sset _t'4 (Ecast (Etempvar _t'5 tint) tbool)))
          (Sset _t'4 (Econst_int (Int.repr 0) tint))))
      (Sset _ret (Etempvar _t'4 tint)))
    (Ssequence
      (Scall None
        (Evar _EVP_MD_CTX_cleanup (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _env_md_ctx_st noattr))
                                      Tnil) tint cc_default))
        ((Eaddrof (Evar _ctx (Tstruct _env_md_ctx_st noattr))
           (tptr (Tstruct _env_md_ctx_st noattr))) :: nil))
      (Sreturn (Some (Etempvar _ret tint))))))
|}.

Definition f_EVP_MD_CTX_md := {|
  fn_return := (tptr (Tstruct _env_md_st noattr));
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Oeq
                 (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
    (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
    Sskip)
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
          (Tstruct _env_md_ctx_st noattr)) _digest
        (tptr (Tstruct _env_md_st noattr))))
    (Sreturn (Some (Etempvar _t'1 (tptr (Tstruct _env_md_st noattr)))))))
|}.

Definition f_EVP_MD_CTX_size := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tuint) :: (_t'1, (tptr (Tstruct _env_md_st noattr))) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _EVP_MD_CTX_md (Tfunction
                             (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                               Tnil) (tptr (Tstruct _env_md_st noattr))
                             cc_default))
      ((Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr))) :: nil))
    (Scall (Some _t'2)
      (Evar _EVP_MD_size (Tfunction
                           (Tcons (tptr (Tstruct _env_md_st noattr)) Tnil)
                           tuint cc_default))
      ((Etempvar _t'1 (tptr (Tstruct _env_md_st noattr))) :: nil)))
  (Sreturn (Some (Etempvar _t'2 tuint))))
|}.

Definition f_EVP_MD_CTX_block_size := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tuint) :: (_t'1, (tptr (Tstruct _env_md_st noattr))) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _EVP_MD_CTX_md (Tfunction
                             (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                               Tnil) (tptr (Tstruct _env_md_st noattr))
                             cc_default))
      ((Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr))) :: nil))
    (Scall (Some _t'2)
      (Evar _EVP_MD_block_size (Tfunction
                                 (Tcons (tptr (Tstruct _env_md_st noattr))
                                   Tnil) tuint cc_default))
      ((Etempvar _t'1 (tptr (Tstruct _env_md_st noattr))) :: nil)))
  (Sreturn (Some (Etempvar _t'2 tuint))))
|}.

Definition f_EVP_MD_CTX_type := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, (tptr (Tstruct _env_md_st noattr))) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _EVP_MD_CTX_md (Tfunction
                             (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                               Tnil) (tptr (Tstruct _env_md_st noattr))
                             cc_default))
      ((Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr))) :: nil))
    (Scall (Some _t'2)
      (Evar _EVP_MD_type (Tfunction
                           (Tcons (tptr (Tstruct _env_md_st noattr)) Tnil)
                           tint cc_default))
      ((Etempvar _t'1 (tptr (Tstruct _env_md_st noattr))) :: nil)))
  (Sreturn (Some (Etempvar _t'2 tint))))
|}.

Definition f_EVP_add_digest := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_digest, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Econst_int (Int.repr 1) tint)))
|}.

Definition composites : list composite_definition :=
(Composite _env_md_ctx_st Struct
   ((_digest, (tptr (Tstruct _env_md_st noattr))) ::
    (_md_data, (tptr tvoid)) ::
    (_pctx, (tptr (Tstruct _evp_pkey_ctx_st noattr))) ::
    (_pctx_ops, (tptr (Tstruct _evp_md_pctx_ops noattr))) :: nil)
   noattr ::
 Composite _env_md_st Struct
   ((_type, tint) :: (_md_size, tuint) :: (_flags, tuint) ::
    (_init,
     (tptr (Tfunction (Tcons (tptr (Tstruct _env_md_ctx_st noattr)) Tnil)
             tvoid cc_default))) ::
    (_update,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
               (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid cc_default))) ::
    (_final,
     (tptr (Tfunction
             (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
               (Tcons (tptr tuchar) Tnil)) tvoid cc_default))) ::
    (_block_size, tuint) :: (_ctx_size, tuint) :: nil)
   noattr ::
 Composite _evp_md_pctx_ops Struct
   ((_free,
     (tptr (Tfunction (Tcons (tptr (Tstruct _evp_pkey_ctx_st noattr)) Tnil)
             tvoid cc_default))) ::
    (_dup,
     (tptr (Tfunction (Tcons (tptr (Tstruct _evp_pkey_ctx_st noattr)) Tnil)
             (tptr (Tstruct _evp_pkey_ctx_st noattr)) cc_default))) :: nil)
   noattr :: nil).

Definition prog : Clight.program := {|
prog_defs :=
((___stringlit_1, Gvar v___stringlit_1) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     None cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tuint (Tcons tuint Tnil)))) tvoid
     cc_default)) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tint :: nil) None cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___compcert_va_int32,
   Gfun(External (EF_external "__compcert_va_int32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_external "__compcert_va_int64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tulong
     cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_external "__compcert_va_float64"
                   (mksignature (AST.Tint :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons (tptr tvoid) Tnil) tdouble
     cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_external "__compcert_va_composite"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     (tptr tvoid) cc_default)) ::
 (___i64_dtos,
   Gfun(External (EF_runtime "__i64_dtos"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tlong cc_default)) ::
 (___i64_dtou,
   Gfun(External (EF_runtime "__i64_dtou"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tdouble Tnil) tulong cc_default)) ::
 (___i64_stod,
   Gfun(External (EF_runtime "__i64_stod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tlong Tnil) tdouble cc_default)) ::
 (___i64_utod,
   Gfun(External (EF_runtime "__i64_utod"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tulong Tnil) tdouble cc_default)) ::
 (___i64_stof,
   Gfun(External (EF_runtime "__i64_stof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tlong Tnil) tfloat cc_default)) ::
 (___i64_utof,
   Gfun(External (EF_runtime "__i64_utof"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tsingle)
                     cc_default)) (Tcons tulong Tnil) tfloat cc_default)) ::
 (___i64_sdiv,
   Gfun(External (EF_runtime "__i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_udiv,
   Gfun(External (EF_runtime "__i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_smod,
   Gfun(External (EF_runtime "__i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_umod,
   Gfun(External (EF_runtime "__i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___i64_shl,
   Gfun(External (EF_runtime "__i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___i64_shr,
   Gfun(External (EF_runtime "__i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tint Tnil)) tulong cc_default)) ::
 (___i64_sar,
   Gfun(External (EF_runtime "__i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tint Tnil)) tlong cc_default)) ::
 (___i64_smulh,
   Gfun(External (EF_runtime "__i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tlong (Tcons tlong Tnil)) tlong cc_default)) ::
 (___i64_umulh,
   Gfun(External (EF_runtime "__i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil)
                     (Some AST.Tlong) cc_default))
     (Tcons tulong (Tcons tulong Tnil)) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tlong)
                     cc_default)) (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) (Some AST.Tint)
                     cc_default)) (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) (Some AST.Tfloat)
                     cc_default)) (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble Tnil)) tdouble cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     (Some AST.Tfloat) cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tushort) Tnil) tushort cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr tuint) Tnil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tushort) (Tcons tushort Tnil))
     tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tuint) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_nop,
   Gfun(External (EF_builtin "__builtin_nop"
                   (mksignature nil None cc_default)) Tnil tvoid cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) None
                     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=true; cc_unproto:=false; cc_structret:=false|})) ::
 (_memcpy,
   Gfun(External (EF_external "memcpy"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
     (tptr tvoid) cc_default)) ::
 (_memset,
   Gfun(External (EF_external "memset"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr tvoid) (Tcons tint (Tcons tuint Tnil))) (tptr tvoid)
     cc_default)) ::
 (_ERR_put_error,
   Gfun(External (EF_external "ERR_put_error"
                   (mksignature
                     (AST.Tint :: AST.Tint :: AST.Tint :: AST.Tint ::
                      AST.Tint :: nil) None cc_default))
     (Tcons tint
       (Tcons tint (Tcons tint (Tcons (tptr tschar) (Tcons tuint Tnil)))))
     tvoid cc_default)) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tuint Tnil) (tptr tvoid) cc_default)) ::
 (_free, Gfun(External EF_free (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (_OPENSSL_cleanse,
   Gfun(External (EF_external "OPENSSL_cleanse"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (_OPENSSL_memcpy, Gfun(Internal f_OPENSSL_memcpy)) ::
 (_OPENSSL_memset, Gfun(Internal f_OPENSSL_memset)) ::
 (_EVP_MD_type, Gfun(Internal f_EVP_MD_type)) ::
 (_EVP_MD_flags, Gfun(Internal f_EVP_MD_flags)) ::
 (_EVP_MD_size, Gfun(Internal f_EVP_MD_size)) ::
 (_EVP_MD_block_size, Gfun(Internal f_EVP_MD_block_size)) ::
 (_EVP_MD_CTX_init, Gfun(Internal f_EVP_MD_CTX_init)) ::
 (_EVP_MD_CTX_create, Gfun(Internal f_EVP_MD_CTX_create)) ::
 (_EVP_MD_CTX_cleanup, Gfun(Internal f_EVP_MD_CTX_cleanup)) ::
 (_EVP_MD_CTX_destroy, Gfun(Internal f_EVP_MD_CTX_destroy)) ::
 (_EVP_MD_CTX_copy_ex, Gfun(Internal f_EVP_MD_CTX_copy_ex)) ::
 (_EVP_MD_CTX_copy, Gfun(Internal f_EVP_MD_CTX_copy)) ::
 (_EVP_DigestInit_ex, Gfun(Internal f_EVP_DigestInit_ex)) ::
 (_EVP_DigestInit, Gfun(Internal f_EVP_DigestInit)) ::
 (_EVP_DigestUpdate, Gfun(Internal f_EVP_DigestUpdate)) ::
 (_EVP_DigestFinal_ex, Gfun(Internal f_EVP_DigestFinal_ex)) ::
 (_EVP_DigestFinal, Gfun(Internal f_EVP_DigestFinal)) ::
 (_EVP_Digest, Gfun(Internal f_EVP_Digest)) ::
 (_EVP_MD_CTX_md, Gfun(Internal f_EVP_MD_CTX_md)) ::
 (_EVP_MD_CTX_size, Gfun(Internal f_EVP_MD_CTX_size)) ::
 (_EVP_MD_CTX_block_size, Gfun(Internal f_EVP_MD_CTX_block_size)) ::
 (_EVP_MD_CTX_type, Gfun(Internal f_EVP_MD_CTX_type)) ::
 (_EVP_add_digest, Gfun(Internal f_EVP_add_digest)) :: nil);
prog_public :=
(_EVP_add_digest :: _EVP_MD_CTX_type :: _EVP_MD_CTX_block_size ::
 _EVP_MD_CTX_size :: _EVP_MD_CTX_md :: _EVP_Digest :: _EVP_DigestFinal ::
 _EVP_DigestFinal_ex :: _EVP_DigestUpdate :: _EVP_DigestInit ::
 _EVP_DigestInit_ex :: _EVP_MD_CTX_copy :: _EVP_MD_CTX_copy_ex ::
 _EVP_MD_CTX_destroy :: _EVP_MD_CTX_cleanup :: _EVP_MD_CTX_create ::
 _EVP_MD_CTX_init :: _EVP_MD_block_size :: _EVP_MD_size :: _EVP_MD_flags ::
 _EVP_MD_type :: _OPENSSL_cleanse :: _free :: _malloc :: _ERR_put_error ::
 _memset :: _memcpy :: ___builtin_debug :: ___builtin_nop ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_fsqrt :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap64 ::
 ___builtin_bswap :: ___i64_umulh :: ___i64_smulh :: ___i64_sar ::
 ___i64_shr :: ___i64_shl :: ___i64_umod :: ___i64_smod :: ___i64_udiv ::
 ___i64_sdiv :: ___i64_utof :: ___i64_stof :: ___i64_utod :: ___i64_stod ::
 ___i64_dtou :: ___i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_memcpy_aligned :: ___builtin_fabs :: nil);
prog_main := _main;
prog_types := composites;
prog_comp_env := make_composite_env composites;
prog_comp_env_eq := refl_equal _
|}.

