
Require Import Clightdefs.
Local Open Scope Z_scope.
Definition _CRYPTO_once : ident := 166%positive.
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
Definition _EVP_md4 : ident := 176%positive.
Definition _EVP_md4_do_init : ident := 174%positive.
Definition _EVP_md4_init : ident := 175%positive.
Definition _EVP_md4_once : ident := 172%positive.
Definition _EVP_md4_once_bss_get : ident := 173%positive.
Definition _EVP_md4_storage : ident := 170%positive.
Definition _EVP_md4_storage_bss_get : ident := 171%positive.
Definition _EVP_md5 : ident := 186%positive.
Definition _EVP_md5_do_init : ident := 184%positive.
Definition _EVP_md5_init : ident := 185%positive.
Definition _EVP_md5_once : ident := 182%positive.
Definition _EVP_md5_once_bss_get : ident := 183%positive.
Definition _EVP_md5_sha1 : ident := 247%positive.
Definition _EVP_md5_sha1_do_init : ident := 245%positive.
Definition _EVP_md5_sha1_init : ident := 246%positive.
Definition _EVP_md5_sha1_once : ident := 243%positive.
Definition _EVP_md5_sha1_once_bss_get : ident := 244%positive.
Definition _EVP_md5_sha1_storage : ident := 241%positive.
Definition _EVP_md5_sha1_storage_bss_get : ident := 242%positive.
Definition _EVP_md5_storage : ident := 180%positive.
Definition _EVP_md5_storage_bss_get : ident := 181%positive.
Definition _EVP_sha1 : ident := 196%positive.
Definition _EVP_sha1_do_init : ident := 194%positive.
Definition _EVP_sha1_init : ident := 195%positive.
Definition _EVP_sha1_once : ident := 192%positive.
Definition _EVP_sha1_once_bss_get : ident := 193%positive.
Definition _EVP_sha1_storage : ident := 190%positive.
Definition _EVP_sha1_storage_bss_get : ident := 191%positive.
Definition _EVP_sha224 : ident := 206%positive.
Definition _EVP_sha224_do_init : ident := 204%positive.
Definition _EVP_sha224_init : ident := 205%positive.
Definition _EVP_sha224_once : ident := 202%positive.
Definition _EVP_sha224_once_bss_get : ident := 203%positive.
Definition _EVP_sha224_storage : ident := 200%positive.
Definition _EVP_sha224_storage_bss_get : ident := 201%positive.
Definition _EVP_sha256 : ident := 216%positive.
Definition _EVP_sha256_do_init : ident := 214%positive.
Definition _EVP_sha256_init : ident := 215%positive.
Definition _EVP_sha256_once : ident := 212%positive.
Definition _EVP_sha256_once_bss_get : ident := 213%positive.
Definition _EVP_sha256_storage : ident := 210%positive.
Definition _EVP_sha256_storage_bss_get : ident := 211%positive.
Definition _EVP_sha384 : ident := 226%positive.
Definition _EVP_sha384_do_init : ident := 224%positive.
Definition _EVP_sha384_init : ident := 225%positive.
Definition _EVP_sha384_once : ident := 222%positive.
Definition _EVP_sha384_once_bss_get : ident := 223%positive.
Definition _EVP_sha384_storage : ident := 220%positive.
Definition _EVP_sha384_storage_bss_get : ident := 221%positive.
Definition _EVP_sha512 : ident := 236%positive.
Definition _EVP_sha512_do_init : ident := 234%positive.
Definition _EVP_sha512_init : ident := 235%positive.
Definition _EVP_sha512_once : ident := 232%positive.
Definition _EVP_sha512_once_bss_get : ident := 233%positive.
Definition _EVP_sha512_storage : ident := 230%positive.
Definition _EVP_sha512_storage_bss_get : ident := 231%positive.
Definition _MD4_Final : ident := 147%positive.
Definition _MD4_Init : ident := 145%positive.
Definition _MD4_Update : ident := 146%positive.
Definition _MD5_Final : ident := 150%positive.
Definition _MD5_Init : ident := 148%positive.
Definition _MD5_Update : ident := 149%positive.
Definition _Nh : ident := 122%positive.
Definition _Nl : ident := 121%positive.
Definition _OPENSSL_cleanse : ident := 74%positive.
Definition _OPENSSL_memcpy : ident := 78%positive.
Definition _OPENSSL_memset : ident := 80%positive.
Definition _SHA1_Final : ident := 153%positive.
Definition _SHA1_Init : ident := 151%positive.
Definition _SHA1_Update : ident := 152%positive.
Definition _SHA224_Final : ident := 156%positive.
Definition _SHA224_Init : ident := 154%positive.
Definition _SHA224_Update : ident := 155%positive.
Definition _SHA256_Final : ident := 159%positive.
Definition _SHA256_Init : ident := 157%positive.
Definition _SHA256_Update : ident := 158%positive.
Definition _SHA384_Final : ident := 162%positive.
Definition _SHA384_Init : ident := 160%positive.
Definition _SHA384_Update : ident := 161%positive.
Definition _SHA512_Final : ident := 165%positive.
Definition _SHA512_Init : ident := 163%positive.
Definition _SHA512_Update : ident := 164%positive.
Definition __2216 : ident := 133%positive.
Definition __2217 : ident := 131%positive.
Definition __2279 : ident := 139%positive.
Definition __2975 : ident := 144%positive.
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
Definition _d : ident := 137%positive.
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
Definition _h : ident := 120%positive.
Definition _h0 : ident := 126%positive.
Definition _h1 : ident := 127%positive.
Definition _h2 : ident := 128%positive.
Definition _h3 : ident := 129%positive.
Definition _h4 : ident := 130%positive.
Definition _impl : ident := 111%positive.
Definition _in : ident := 92%positive.
Definition _init : ident := 12%positive.
Definition _len : ident := 102%positive.
Definition _main : ident := 119%positive.
Definition _malloc : ident := 73%positive.
Definition _md : ident := 81%positive.
Definition _md4_final : ident := 169%positive.
Definition _md4_init : ident := 167%positive.
Definition _md4_state_st : ident := 124%positive.
Definition _md4_update : ident := 168%positive.
Definition _md5 : ident := 142%positive.
Definition _md5_final : ident := 179%positive.
Definition _md5_init : ident := 177%positive.
Definition _md5_sha1_final : ident := 240%positive.
Definition _md5_sha1_init : ident := 238%positive.
Definition _md5_sha1_update : ident := 239%positive.
Definition _md5_state_st : ident := 125%positive.
Definition _md5_update : ident := 178%positive.
Definition _md_ctx : ident := 237%positive.
Definition _md_data : ident := 3%positive.
Definition _md_len : ident := 135%positive.
Definition _md_out : ident := 104%positive.
Definition _md_size : ident := 10%positive.
Definition _memcpy : ident := 70%positive.
Definition _memset : ident := 71%positive.
Definition _n : ident := 77%positive.
Definition _num : ident := 123%positive.
Definition _out : ident := 91%positive.
Definition _out_md : ident := 109%positive.
Definition _out_size : ident := 110%positive.
Definition _p : ident := 138%positive.
Definition _pctx : ident := 5%positive.
Definition _pctx_ops : ident := 7%positive.
Definition _ret : ident := 112%positive.
Definition _sha1 : ident := 143%positive.
Definition _sha1_final : ident := 189%positive.
Definition _sha1_init : ident := 187%positive.
Definition _sha1_update : ident := 188%positive.
Definition _sha224_final : ident := 199%positive.
Definition _sha224_init : ident := 197%positive.
Definition _sha224_update : ident := 198%positive.
Definition _sha256_final : ident := 209%positive.
Definition _sha256_init : ident := 207%positive.
Definition _sha256_state_st : ident := 136%positive.
Definition _sha256_update : ident := 208%positive.
Definition _sha384_final : ident := 219%positive.
Definition _sha384_init : ident := 217%positive.
Definition _sha384_update : ident := 218%positive.
Definition _sha512_final : ident := 229%positive.
Definition _sha512_init : ident := 227%positive.
Definition _sha512_state_st : ident := 141%positive.
Definition _sha512_update : ident := 228%positive.
Definition _sha_state_st : ident := 134%positive.
Definition _size : ident := 105%positive.
Definition _src : ident := 76%positive.
Definition _tmp_buf : ident := 93%positive.
Definition _type : ident := 9%positive.
Definition _u : ident := 140%positive.
Definition _update : ident := 13%positive.
Definition _t'1 : ident := 248%positive.
Definition _t'2 : ident := 249%positive.
Definition _t'3 : ident := 250%positive.

Definition f_md4_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Scall (Some _t'1)
    (Evar _MD4_Init (Tfunction
                      (Tcons (tptr (Tstruct _md4_state_st noattr)) Tnil) tint
                      cc_default)) ((Etempvar _t'2 (tptr tvoid)) :: nil)))
|}.

Definition f_md4_update := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_data, (tptr tvoid)) :: (_count, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Scall (Some _t'1)
    (Evar _MD4_Update (Tfunction
                        (Tcons (tptr (Tstruct _md4_state_st noattr))
                          (Tcons (tptr tvoid) (Tcons tuint Tnil))) tint
                        cc_default))
    ((Etempvar _t'2 (tptr tvoid)) :: (Etempvar _data (tptr tvoid)) ::
     (Etempvar _count tuint) :: nil)))
|}.

Definition f_md4_final := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_out, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Scall (Some _t'1)
    (Evar _MD4_Final (Tfunction
                       (Tcons (tptr tuchar)
                         (Tcons (tptr (Tstruct _md4_state_st noattr)) Tnil))
                       tint cc_default))
    ((Etempvar _out (tptr tuchar)) :: (Etempvar _t'2 (tptr tvoid)) :: nil)))
|}.

Definition v_EVP_md4_storage := {|
  gvar_info := (Tstruct _env_md_st noattr);
  gvar_init := (Init_space 32 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_EVP_md4_storage_bss_get := {|
  fn_return := (tptr (Tstruct _env_md_st noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eaddrof (Evar _EVP_md4_storage (Tstruct _env_md_st noattr))
                 (tptr (Tstruct _env_md_st noattr)))))
|}.

Definition v_EVP_md4_once := {|
  gvar_info := tuint;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_EVP_md4_once_bss_get := {|
  fn_return := (tptr tuint);
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eaddrof (Evar _EVP_md4_once tuint) (tptr tuint))))
|}.

Definition f_EVP_md4_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _EVP_md4_storage_bss_get (Tfunction Tnil
                                     (tptr (Tstruct _env_md_st noattr))
                                     cc_default)) nil)
  (Scall None
    (Evar _EVP_md4_do_init (Tfunction
                             (Tcons (tptr (Tstruct _env_md_st noattr)) Tnil)
                             tvoid cc_default))
    ((Etempvar _t'1 (tptr (Tstruct _env_md_st noattr))) :: nil)))
|}.

Definition f_EVP_md4 := {|
  fn_return := (tptr (Tstruct _env_md_st noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'1, (tptr tuint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _EVP_md4_once_bss_get (Tfunction Tnil (tptr tuint) cc_default))
      nil)
    (Scall None
      (Evar _CRYPTO_once (Tfunction
                           (Tcons (tptr tuint)
                             (Tcons (tptr (Tfunction Tnil tvoid cc_default))
                               Tnil)) tvoid cc_default))
      ((Etempvar _t'1 (tptr tuint)) ::
       (Evar _EVP_md4_init (Tfunction Tnil tvoid cc_default)) :: nil)))
  (Ssequence
    (Scall (Some _t'2)
      (Evar _EVP_md4_storage_bss_get (Tfunction Tnil
                                       (tptr (Tstruct _env_md_st noattr))
                                       cc_default)) nil)
    (Sreturn (Some (Ecast (Etempvar _t'2 (tptr (Tstruct _env_md_st noattr)))
                     (tptr (Tstruct _env_md_st noattr)))))))
|}.

Definition f_EVP_md4_do_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
        (Tstruct _env_md_st noattr)) _type tint)
    (Econst_int (Int.repr 257) tint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
          (Tstruct _env_md_st noattr)) _md_size tuint)
      (Econst_int (Int.repr 16) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
            (Tstruct _env_md_st noattr)) _flags tuint)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
              (Tstruct _env_md_st noattr)) _init
            (tptr (Tfunction
                    (Tcons (tptr (Tstruct _env_md_ctx_st noattr)) Tnil) tvoid
                    cc_default)))
          (Evar _md4_init (Tfunction
                            (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                              Tnil) tvoid cc_default)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                (Tstruct _env_md_st noattr)) _update
              (tptr (Tfunction
                      (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                        (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                      cc_default)))
            (Evar _md4_update (Tfunction
                                (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                                  (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                tvoid cc_default)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                  (Tstruct _env_md_st noattr)) _final
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                          (Tcons (tptr tuchar) Tnil)) tvoid cc_default)))
              (Evar _md4_final (Tfunction
                                 (Tcons
                                   (tptr (Tstruct _env_md_ctx_st noattr))
                                   (Tcons (tptr tuchar) Tnil)) tvoid
                                 cc_default)))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                    (Tstruct _env_md_st noattr)) _block_size tuint)
                (Econst_int (Int.repr 64) tint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                    (Tstruct _env_md_st noattr)) _ctx_size tuint)
                (Esizeof (Tstruct _md4_state_st noattr) tuint)))))))))
|}.

Definition f_md5_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Scall (Some _t'1)
    (Evar _MD5_Init (Tfunction
                      (Tcons (tptr (Tstruct _md5_state_st noattr)) Tnil) tint
                      cc_default)) ((Etempvar _t'2 (tptr tvoid)) :: nil)))
|}.

Definition f_md5_update := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_data, (tptr tvoid)) :: (_count, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Scall (Some _t'1)
    (Evar _MD5_Update (Tfunction
                        (Tcons (tptr (Tstruct _md5_state_st noattr))
                          (Tcons (tptr tvoid) (Tcons tuint Tnil))) tint
                        cc_default))
    ((Etempvar _t'2 (tptr tvoid)) :: (Etempvar _data (tptr tvoid)) ::
     (Etempvar _count tuint) :: nil)))
|}.

Definition f_md5_final := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_out, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Scall (Some _t'1)
    (Evar _MD5_Final (Tfunction
                       (Tcons (tptr tuchar)
                         (Tcons (tptr (Tstruct _md5_state_st noattr)) Tnil))
                       tint cc_default))
    ((Etempvar _out (tptr tuchar)) :: (Etempvar _t'2 (tptr tvoid)) :: nil)))
|}.

Definition v_EVP_md5_storage := {|
  gvar_info := (Tstruct _env_md_st noattr);
  gvar_init := (Init_space 32 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_EVP_md5_storage_bss_get := {|
  fn_return := (tptr (Tstruct _env_md_st noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eaddrof (Evar _EVP_md5_storage (Tstruct _env_md_st noattr))
                 (tptr (Tstruct _env_md_st noattr)))))
|}.

Definition v_EVP_md5_once := {|
  gvar_info := tuint;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_EVP_md5_once_bss_get := {|
  fn_return := (tptr tuint);
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eaddrof (Evar _EVP_md5_once tuint) (tptr tuint))))
|}.

Definition f_EVP_md5_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _EVP_md5_storage_bss_get (Tfunction Tnil
                                     (tptr (Tstruct _env_md_st noattr))
                                     cc_default)) nil)
  (Scall None
    (Evar _EVP_md5_do_init (Tfunction
                             (Tcons (tptr (Tstruct _env_md_st noattr)) Tnil)
                             tvoid cc_default))
    ((Etempvar _t'1 (tptr (Tstruct _env_md_st noattr))) :: nil)))
|}.

Definition f_EVP_md5 := {|
  fn_return := (tptr (Tstruct _env_md_st noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'1, (tptr tuint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _EVP_md5_once_bss_get (Tfunction Tnil (tptr tuint) cc_default))
      nil)
    (Scall None
      (Evar _CRYPTO_once (Tfunction
                           (Tcons (tptr tuint)
                             (Tcons (tptr (Tfunction Tnil tvoid cc_default))
                               Tnil)) tvoid cc_default))
      ((Etempvar _t'1 (tptr tuint)) ::
       (Evar _EVP_md5_init (Tfunction Tnil tvoid cc_default)) :: nil)))
  (Ssequence
    (Scall (Some _t'2)
      (Evar _EVP_md5_storage_bss_get (Tfunction Tnil
                                       (tptr (Tstruct _env_md_st noattr))
                                       cc_default)) nil)
    (Sreturn (Some (Ecast (Etempvar _t'2 (tptr (Tstruct _env_md_st noattr)))
                     (tptr (Tstruct _env_md_st noattr)))))))
|}.

Definition f_EVP_md5_do_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
        (Tstruct _env_md_st noattr)) _type tint)
    (Econst_int (Int.repr 4) tint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
          (Tstruct _env_md_st noattr)) _md_size tuint)
      (Econst_int (Int.repr 16) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
            (Tstruct _env_md_st noattr)) _flags tuint)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
              (Tstruct _env_md_st noattr)) _init
            (tptr (Tfunction
                    (Tcons (tptr (Tstruct _env_md_ctx_st noattr)) Tnil) tvoid
                    cc_default)))
          (Evar _md5_init (Tfunction
                            (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                              Tnil) tvoid cc_default)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                (Tstruct _env_md_st noattr)) _update
              (tptr (Tfunction
                      (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                        (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                      cc_default)))
            (Evar _md5_update (Tfunction
                                (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                                  (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                tvoid cc_default)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                  (Tstruct _env_md_st noattr)) _final
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                          (Tcons (tptr tuchar) Tnil)) tvoid cc_default)))
              (Evar _md5_final (Tfunction
                                 (Tcons
                                   (tptr (Tstruct _env_md_ctx_st noattr))
                                   (Tcons (tptr tuchar) Tnil)) tvoid
                                 cc_default)))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                    (Tstruct _env_md_st noattr)) _block_size tuint)
                (Econst_int (Int.repr 64) tint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                    (Tstruct _env_md_st noattr)) _ctx_size tuint)
                (Esizeof (Tstruct _md5_state_st noattr) tuint)))))))))
|}.

Definition f_sha1_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Scall (Some _t'1)
    (Evar _SHA1_Init (Tfunction
                       (Tcons (tptr (Tstruct _sha_state_st noattr)) Tnil)
                       tint cc_default))
    ((Etempvar _t'2 (tptr tvoid)) :: nil)))
|}.

Definition f_sha1_update := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_data, (tptr tvoid)) :: (_count, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Scall (Some _t'1)
    (Evar _SHA1_Update (Tfunction
                         (Tcons (tptr (Tstruct _sha_state_st noattr))
                           (Tcons (tptr tvoid) (Tcons tuint Tnil))) tint
                         cc_default))
    ((Etempvar _t'2 (tptr tvoid)) :: (Etempvar _data (tptr tvoid)) ::
     (Etempvar _count tuint) :: nil)))
|}.

Definition f_sha1_final := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_md, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Scall (Some _t'1)
    (Evar _SHA1_Final (Tfunction
                        (Tcons (tptr tuchar)
                          (Tcons (tptr (Tstruct _sha_state_st noattr)) Tnil))
                        tint cc_default))
    ((Etempvar _md (tptr tuchar)) :: (Etempvar _t'2 (tptr tvoid)) :: nil)))
|}.

Definition v_EVP_sha1_storage := {|
  gvar_info := (Tstruct _env_md_st noattr);
  gvar_init := (Init_space 32 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_EVP_sha1_storage_bss_get := {|
  fn_return := (tptr (Tstruct _env_md_st noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eaddrof (Evar _EVP_sha1_storage (Tstruct _env_md_st noattr))
                 (tptr (Tstruct _env_md_st noattr)))))
|}.

Definition v_EVP_sha1_once := {|
  gvar_info := tuint;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_EVP_sha1_once_bss_get := {|
  fn_return := (tptr tuint);
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eaddrof (Evar _EVP_sha1_once tuint) (tptr tuint))))
|}.

Definition f_EVP_sha1_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _EVP_sha1_storage_bss_get (Tfunction Tnil
                                      (tptr (Tstruct _env_md_st noattr))
                                      cc_default)) nil)
  (Scall None
    (Evar _EVP_sha1_do_init (Tfunction
                              (Tcons (tptr (Tstruct _env_md_st noattr)) Tnil)
                              tvoid cc_default))
    ((Etempvar _t'1 (tptr (Tstruct _env_md_st noattr))) :: nil)))
|}.

Definition f_EVP_sha1 := {|
  fn_return := (tptr (Tstruct _env_md_st noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'1, (tptr tuint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _EVP_sha1_once_bss_get (Tfunction Tnil (tptr tuint) cc_default))
      nil)
    (Scall None
      (Evar _CRYPTO_once (Tfunction
                           (Tcons (tptr tuint)
                             (Tcons (tptr (Tfunction Tnil tvoid cc_default))
                               Tnil)) tvoid cc_default))
      ((Etempvar _t'1 (tptr tuint)) ::
       (Evar _EVP_sha1_init (Tfunction Tnil tvoid cc_default)) :: nil)))
  (Ssequence
    (Scall (Some _t'2)
      (Evar _EVP_sha1_storage_bss_get (Tfunction Tnil
                                        (tptr (Tstruct _env_md_st noattr))
                                        cc_default)) nil)
    (Sreturn (Some (Ecast (Etempvar _t'2 (tptr (Tstruct _env_md_st noattr)))
                     (tptr (Tstruct _env_md_st noattr)))))))
|}.

Definition f_EVP_sha1_do_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
        (Tstruct _env_md_st noattr)) _type tint)
    (Econst_int (Int.repr 64) tint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
          (Tstruct _env_md_st noattr)) _md_size tuint)
      (Econst_int (Int.repr 20) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
            (Tstruct _env_md_st noattr)) _flags tuint)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
              (Tstruct _env_md_st noattr)) _init
            (tptr (Tfunction
                    (Tcons (tptr (Tstruct _env_md_ctx_st noattr)) Tnil) tvoid
                    cc_default)))
          (Evar _sha1_init (Tfunction
                             (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                               Tnil) tvoid cc_default)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                (Tstruct _env_md_st noattr)) _update
              (tptr (Tfunction
                      (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                        (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                      cc_default)))
            (Evar _sha1_update (Tfunction
                                 (Tcons
                                   (tptr (Tstruct _env_md_ctx_st noattr))
                                   (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                 tvoid cc_default)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                  (Tstruct _env_md_st noattr)) _final
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                          (Tcons (tptr tuchar) Tnil)) tvoid cc_default)))
              (Evar _sha1_final (Tfunction
                                  (Tcons
                                    (tptr (Tstruct _env_md_ctx_st noattr))
                                    (Tcons (tptr tuchar) Tnil)) tvoid
                                  cc_default)))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                    (Tstruct _env_md_st noattr)) _block_size tuint)
                (Econst_int (Int.repr 64) tint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                    (Tstruct _env_md_st noattr)) _ctx_size tuint)
                (Esizeof (Tstruct _sha_state_st noattr) tuint)))))))))
|}.

Definition f_sha224_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Scall (Some _t'1)
    (Evar _SHA224_Init (Tfunction
                         (Tcons (tptr (Tstruct _sha256_state_st noattr))
                           Tnil) tint cc_default))
    ((Etempvar _t'2 (tptr tvoid)) :: nil)))
|}.

Definition f_sha224_update := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_data, (tptr tvoid)) :: (_count, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Scall (Some _t'1)
    (Evar _SHA224_Update (Tfunction
                           (Tcons (tptr (Tstruct _sha256_state_st noattr))
                             (Tcons (tptr tvoid) (Tcons tuint Tnil))) tint
                           cc_default))
    ((Etempvar _t'2 (tptr tvoid)) :: (Etempvar _data (tptr tvoid)) ::
     (Etempvar _count tuint) :: nil)))
|}.

Definition f_sha224_final := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_md, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Scall (Some _t'1)
    (Evar _SHA224_Final (Tfunction
                          (Tcons (tptr tuchar)
                            (Tcons (tptr (Tstruct _sha256_state_st noattr))
                              Tnil)) tint cc_default))
    ((Etempvar _md (tptr tuchar)) :: (Etempvar _t'2 (tptr tvoid)) :: nil)))
|}.

Definition v_EVP_sha224_storage := {|
  gvar_info := (Tstruct _env_md_st noattr);
  gvar_init := (Init_space 32 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_EVP_sha224_storage_bss_get := {|
  fn_return := (tptr (Tstruct _env_md_st noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eaddrof
                 (Evar _EVP_sha224_storage (Tstruct _env_md_st noattr))
                 (tptr (Tstruct _env_md_st noattr)))))
|}.

Definition v_EVP_sha224_once := {|
  gvar_info := tuint;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_EVP_sha224_once_bss_get := {|
  fn_return := (tptr tuint);
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eaddrof (Evar _EVP_sha224_once tuint) (tptr tuint))))
|}.

Definition f_EVP_sha224_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _EVP_sha224_storage_bss_get (Tfunction Tnil
                                        (tptr (Tstruct _env_md_st noattr))
                                        cc_default)) nil)
  (Scall None
    (Evar _EVP_sha224_do_init (Tfunction
                                (Tcons (tptr (Tstruct _env_md_st noattr))
                                  Tnil) tvoid cc_default))
    ((Etempvar _t'1 (tptr (Tstruct _env_md_st noattr))) :: nil)))
|}.

Definition f_EVP_sha224 := {|
  fn_return := (tptr (Tstruct _env_md_st noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'1, (tptr tuint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _EVP_sha224_once_bss_get (Tfunction Tnil (tptr tuint) cc_default))
      nil)
    (Scall None
      (Evar _CRYPTO_once (Tfunction
                           (Tcons (tptr tuint)
                             (Tcons (tptr (Tfunction Tnil tvoid cc_default))
                               Tnil)) tvoid cc_default))
      ((Etempvar _t'1 (tptr tuint)) ::
       (Evar _EVP_sha224_init (Tfunction Tnil tvoid cc_default)) :: nil)))
  (Ssequence
    (Scall (Some _t'2)
      (Evar _EVP_sha224_storage_bss_get (Tfunction Tnil
                                          (tptr (Tstruct _env_md_st noattr))
                                          cc_default)) nil)
    (Sreturn (Some (Ecast (Etempvar _t'2 (tptr (Tstruct _env_md_st noattr)))
                     (tptr (Tstruct _env_md_st noattr)))))))
|}.

Definition f_EVP_sha224_do_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
        (Tstruct _env_md_st noattr)) _type tint)
    (Econst_int (Int.repr 675) tint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
          (Tstruct _env_md_st noattr)) _md_size tuint)
      (Econst_int (Int.repr 28) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
            (Tstruct _env_md_st noattr)) _flags tuint)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
              (Tstruct _env_md_st noattr)) _init
            (tptr (Tfunction
                    (Tcons (tptr (Tstruct _env_md_ctx_st noattr)) Tnil) tvoid
                    cc_default)))
          (Evar _sha224_init (Tfunction
                               (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                                 Tnil) tvoid cc_default)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                (Tstruct _env_md_st noattr)) _update
              (tptr (Tfunction
                      (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                        (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                      cc_default)))
            (Evar _sha224_update (Tfunction
                                   (Tcons
                                     (tptr (Tstruct _env_md_ctx_st noattr))
                                     (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                   tvoid cc_default)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                  (Tstruct _env_md_st noattr)) _final
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                          (Tcons (tptr tuchar) Tnil)) tvoid cc_default)))
              (Evar _sha224_final (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _env_md_ctx_st noattr))
                                      (Tcons (tptr tuchar) Tnil)) tvoid
                                    cc_default)))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                    (Tstruct _env_md_st noattr)) _block_size tuint)
                (Econst_int (Int.repr 64) tint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                    (Tstruct _env_md_st noattr)) _ctx_size tuint)
                (Esizeof (Tstruct _sha256_state_st noattr) tuint)))))))))
|}.

Definition f_sha256_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Scall (Some _t'1)
    (Evar _SHA256_Init (Tfunction
                         (Tcons (tptr (Tstruct _sha256_state_st noattr))
                           Tnil) tint cc_default))
    ((Etempvar _t'2 (tptr tvoid)) :: nil)))
|}.

Definition f_sha256_update := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_data, (tptr tvoid)) :: (_count, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Scall (Some _t'1)
    (Evar _SHA256_Update (Tfunction
                           (Tcons (tptr (Tstruct _sha256_state_st noattr))
                             (Tcons (tptr tvoid) (Tcons tuint Tnil))) tint
                           cc_default))
    ((Etempvar _t'2 (tptr tvoid)) :: (Etempvar _data (tptr tvoid)) ::
     (Etempvar _count tuint) :: nil)))
|}.

Definition f_sha256_final := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_md, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Scall (Some _t'1)
    (Evar _SHA256_Final (Tfunction
                          (Tcons (tptr tuchar)
                            (Tcons (tptr (Tstruct _sha256_state_st noattr))
                              Tnil)) tint cc_default))
    ((Etempvar _md (tptr tuchar)) :: (Etempvar _t'2 (tptr tvoid)) :: nil)))
|}.

Definition v_EVP_sha256_storage := {|
  gvar_info := (Tstruct _env_md_st noattr);
  gvar_init := (Init_space 32 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_EVP_sha256_storage_bss_get := {|
  fn_return := (tptr (Tstruct _env_md_st noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eaddrof
                 (Evar _EVP_sha256_storage (Tstruct _env_md_st noattr))
                 (tptr (Tstruct _env_md_st noattr)))))
|}.

Definition v_EVP_sha256_once := {|
  gvar_info := tuint;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_EVP_sha256_once_bss_get := {|
  fn_return := (tptr tuint);
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eaddrof (Evar _EVP_sha256_once tuint) (tptr tuint))))
|}.

Definition f_EVP_sha256_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _EVP_sha256_storage_bss_get (Tfunction Tnil
                                        (tptr (Tstruct _env_md_st noattr))
                                        cc_default)) nil)
  (Scall None
    (Evar _EVP_sha256_do_init (Tfunction
                                (Tcons (tptr (Tstruct _env_md_st noattr))
                                  Tnil) tvoid cc_default))
    ((Etempvar _t'1 (tptr (Tstruct _env_md_st noattr))) :: nil)))
|}.

Definition f_EVP_sha256 := {|
  fn_return := (tptr (Tstruct _env_md_st noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'1, (tptr tuint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _EVP_sha256_once_bss_get (Tfunction Tnil (tptr tuint) cc_default))
      nil)
    (Scall None
      (Evar _CRYPTO_once (Tfunction
                           (Tcons (tptr tuint)
                             (Tcons (tptr (Tfunction Tnil tvoid cc_default))
                               Tnil)) tvoid cc_default))
      ((Etempvar _t'1 (tptr tuint)) ::
       (Evar _EVP_sha256_init (Tfunction Tnil tvoid cc_default)) :: nil)))
  (Ssequence
    (Scall (Some _t'2)
      (Evar _EVP_sha256_storage_bss_get (Tfunction Tnil
                                          (tptr (Tstruct _env_md_st noattr))
                                          cc_default)) nil)
    (Sreturn (Some (Ecast (Etempvar _t'2 (tptr (Tstruct _env_md_st noattr)))
                     (tptr (Tstruct _env_md_st noattr)))))))
|}.

Definition f_EVP_sha256_do_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
        (Tstruct _env_md_st noattr)) _type tint)
    (Econst_int (Int.repr 672) tint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
          (Tstruct _env_md_st noattr)) _md_size tuint)
      (Econst_int (Int.repr 32) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
            (Tstruct _env_md_st noattr)) _flags tuint)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
              (Tstruct _env_md_st noattr)) _init
            (tptr (Tfunction
                    (Tcons (tptr (Tstruct _env_md_ctx_st noattr)) Tnil) tvoid
                    cc_default)))
          (Evar _sha256_init (Tfunction
                               (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                                 Tnil) tvoid cc_default)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                (Tstruct _env_md_st noattr)) _update
              (tptr (Tfunction
                      (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                        (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                      cc_default)))
            (Evar _sha256_update (Tfunction
                                   (Tcons
                                     (tptr (Tstruct _env_md_ctx_st noattr))
                                     (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                   tvoid cc_default)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                  (Tstruct _env_md_st noattr)) _final
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                          (Tcons (tptr tuchar) Tnil)) tvoid cc_default)))
              (Evar _sha256_final (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _env_md_ctx_st noattr))
                                      (Tcons (tptr tuchar) Tnil)) tvoid
                                    cc_default)))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                    (Tstruct _env_md_st noattr)) _block_size tuint)
                (Econst_int (Int.repr 64) tint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                    (Tstruct _env_md_st noattr)) _ctx_size tuint)
                (Esizeof (Tstruct _sha256_state_st noattr) tuint)))))))))
|}.

Definition f_sha384_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Scall (Some _t'1)
    (Evar _SHA384_Init (Tfunction
                         (Tcons (tptr (Tstruct _sha512_state_st noattr))
                           Tnil) tint cc_default))
    ((Etempvar _t'2 (tptr tvoid)) :: nil)))
|}.

Definition f_sha384_update := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_data, (tptr tvoid)) :: (_count, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Scall (Some _t'1)
    (Evar _SHA384_Update (Tfunction
                           (Tcons (tptr (Tstruct _sha512_state_st noattr))
                             (Tcons (tptr tvoid) (Tcons tuint Tnil))) tint
                           cc_default))
    ((Etempvar _t'2 (tptr tvoid)) :: (Etempvar _data (tptr tvoid)) ::
     (Etempvar _count tuint) :: nil)))
|}.

Definition f_sha384_final := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_md, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Scall (Some _t'1)
    (Evar _SHA384_Final (Tfunction
                          (Tcons (tptr tuchar)
                            (Tcons (tptr (Tstruct _sha512_state_st noattr))
                              Tnil)) tint cc_default))
    ((Etempvar _md (tptr tuchar)) :: (Etempvar _t'2 (tptr tvoid)) :: nil)))
|}.

Definition v_EVP_sha384_storage := {|
  gvar_info := (Tstruct _env_md_st noattr);
  gvar_init := (Init_space 32 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_EVP_sha384_storage_bss_get := {|
  fn_return := (tptr (Tstruct _env_md_st noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eaddrof
                 (Evar _EVP_sha384_storage (Tstruct _env_md_st noattr))
                 (tptr (Tstruct _env_md_st noattr)))))
|}.

Definition v_EVP_sha384_once := {|
  gvar_info := tuint;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_EVP_sha384_once_bss_get := {|
  fn_return := (tptr tuint);
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eaddrof (Evar _EVP_sha384_once tuint) (tptr tuint))))
|}.

Definition f_EVP_sha384_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _EVP_sha384_storage_bss_get (Tfunction Tnil
                                        (tptr (Tstruct _env_md_st noattr))
                                        cc_default)) nil)
  (Scall None
    (Evar _EVP_sha384_do_init (Tfunction
                                (Tcons (tptr (Tstruct _env_md_st noattr))
                                  Tnil) tvoid cc_default))
    ((Etempvar _t'1 (tptr (Tstruct _env_md_st noattr))) :: nil)))
|}.

Definition f_EVP_sha384 := {|
  fn_return := (tptr (Tstruct _env_md_st noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'1, (tptr tuint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _EVP_sha384_once_bss_get (Tfunction Tnil (tptr tuint) cc_default))
      nil)
    (Scall None
      (Evar _CRYPTO_once (Tfunction
                           (Tcons (tptr tuint)
                             (Tcons (tptr (Tfunction Tnil tvoid cc_default))
                               Tnil)) tvoid cc_default))
      ((Etempvar _t'1 (tptr tuint)) ::
       (Evar _EVP_sha384_init (Tfunction Tnil tvoid cc_default)) :: nil)))
  (Ssequence
    (Scall (Some _t'2)
      (Evar _EVP_sha384_storage_bss_get (Tfunction Tnil
                                          (tptr (Tstruct _env_md_st noattr))
                                          cc_default)) nil)
    (Sreturn (Some (Ecast (Etempvar _t'2 (tptr (Tstruct _env_md_st noattr)))
                     (tptr (Tstruct _env_md_st noattr)))))))
|}.

Definition f_EVP_sha384_do_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
        (Tstruct _env_md_st noattr)) _type tint)
    (Econst_int (Int.repr 673) tint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
          (Tstruct _env_md_st noattr)) _md_size tuint)
      (Econst_int (Int.repr 48) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
            (Tstruct _env_md_st noattr)) _flags tuint)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
              (Tstruct _env_md_st noattr)) _init
            (tptr (Tfunction
                    (Tcons (tptr (Tstruct _env_md_ctx_st noattr)) Tnil) tvoid
                    cc_default)))
          (Evar _sha384_init (Tfunction
                               (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                                 Tnil) tvoid cc_default)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                (Tstruct _env_md_st noattr)) _update
              (tptr (Tfunction
                      (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                        (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                      cc_default)))
            (Evar _sha384_update (Tfunction
                                   (Tcons
                                     (tptr (Tstruct _env_md_ctx_st noattr))
                                     (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                   tvoid cc_default)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                  (Tstruct _env_md_st noattr)) _final
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                          (Tcons (tptr tuchar) Tnil)) tvoid cc_default)))
              (Evar _sha384_final (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _env_md_ctx_st noattr))
                                      (Tcons (tptr tuchar) Tnil)) tvoid
                                    cc_default)))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                    (Tstruct _env_md_st noattr)) _block_size tuint)
                (Econst_int (Int.repr 128) tint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                    (Tstruct _env_md_st noattr)) _ctx_size tuint)
                (Esizeof (Tstruct _sha512_state_st noattr) tuint)))))))))
|}.

Definition f_sha512_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Scall (Some _t'1)
    (Evar _SHA512_Init (Tfunction
                         (Tcons (tptr (Tstruct _sha512_state_st noattr))
                           Tnil) tint cc_default))
    ((Etempvar _t'2 (tptr tvoid)) :: nil)))
|}.

Definition f_sha512_update := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_data, (tptr tvoid)) :: (_count, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Scall (Some _t'1)
    (Evar _SHA512_Update (Tfunction
                           (Tcons (tptr (Tstruct _sha512_state_st noattr))
                             (Tcons (tptr tvoid) (Tcons tuint Tnil))) tint
                           cc_default))
    ((Etempvar _t'2 (tptr tvoid)) :: (Etempvar _data (tptr tvoid)) ::
     (Etempvar _count tuint) :: nil)))
|}.

Definition f_sha512_final := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_md, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: (_t'2, (tptr tvoid)) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'2
    (Efield
      (Ederef (Etempvar _ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Scall (Some _t'1)
    (Evar _SHA512_Final (Tfunction
                          (Tcons (tptr tuchar)
                            (Tcons (tptr (Tstruct _sha512_state_st noattr))
                              Tnil)) tint cc_default))
    ((Etempvar _md (tptr tuchar)) :: (Etempvar _t'2 (tptr tvoid)) :: nil)))
|}.

Definition v_EVP_sha512_storage := {|
  gvar_info := (Tstruct _env_md_st noattr);
  gvar_init := (Init_space 32 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_EVP_sha512_storage_bss_get := {|
  fn_return := (tptr (Tstruct _env_md_st noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eaddrof
                 (Evar _EVP_sha512_storage (Tstruct _env_md_st noattr))
                 (tptr (Tstruct _env_md_st noattr)))))
|}.

Definition v_EVP_sha512_once := {|
  gvar_info := tuint;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_EVP_sha512_once_bss_get := {|
  fn_return := (tptr tuint);
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eaddrof (Evar _EVP_sha512_once tuint) (tptr tuint))))
|}.

Definition f_EVP_sha512_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _EVP_sha512_storage_bss_get (Tfunction Tnil
                                        (tptr (Tstruct _env_md_st noattr))
                                        cc_default)) nil)
  (Scall None
    (Evar _EVP_sha512_do_init (Tfunction
                                (Tcons (tptr (Tstruct _env_md_st noattr))
                                  Tnil) tvoid cc_default))
    ((Etempvar _t'1 (tptr (Tstruct _env_md_st noattr))) :: nil)))
|}.

Definition f_EVP_sha512 := {|
  fn_return := (tptr (Tstruct _env_md_st noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'1, (tptr tuint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _EVP_sha512_once_bss_get (Tfunction Tnil (tptr tuint) cc_default))
      nil)
    (Scall None
      (Evar _CRYPTO_once (Tfunction
                           (Tcons (tptr tuint)
                             (Tcons (tptr (Tfunction Tnil tvoid cc_default))
                               Tnil)) tvoid cc_default))
      ((Etempvar _t'1 (tptr tuint)) ::
       (Evar _EVP_sha512_init (Tfunction Tnil tvoid cc_default)) :: nil)))
  (Ssequence
    (Scall (Some _t'2)
      (Evar _EVP_sha512_storage_bss_get (Tfunction Tnil
                                          (tptr (Tstruct _env_md_st noattr))
                                          cc_default)) nil)
    (Sreturn (Some (Ecast (Etempvar _t'2 (tptr (Tstruct _env_md_st noattr)))
                     (tptr (Tstruct _env_md_st noattr)))))))
|}.

Definition f_EVP_sha512_do_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
        (Tstruct _env_md_st noattr)) _type tint)
    (Econst_int (Int.repr 674) tint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
          (Tstruct _env_md_st noattr)) _md_size tuint)
      (Econst_int (Int.repr 64) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
            (Tstruct _env_md_st noattr)) _flags tuint)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
              (Tstruct _env_md_st noattr)) _init
            (tptr (Tfunction
                    (Tcons (tptr (Tstruct _env_md_ctx_st noattr)) Tnil) tvoid
                    cc_default)))
          (Evar _sha512_init (Tfunction
                               (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                                 Tnil) tvoid cc_default)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                (Tstruct _env_md_st noattr)) _update
              (tptr (Tfunction
                      (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                        (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                      cc_default)))
            (Evar _sha512_update (Tfunction
                                   (Tcons
                                     (tptr (Tstruct _env_md_ctx_st noattr))
                                     (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                   tvoid cc_default)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                  (Tstruct _env_md_st noattr)) _final
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                          (Tcons (tptr tuchar) Tnil)) tvoid cc_default)))
              (Evar _sha512_final (Tfunction
                                    (Tcons
                                      (tptr (Tstruct _env_md_ctx_st noattr))
                                      (Tcons (tptr tuchar) Tnil)) tvoid
                                    cc_default)))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                    (Tstruct _env_md_st noattr)) _block_size tuint)
                (Econst_int (Int.repr 128) tint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                    (Tstruct _env_md_st noattr)) _ctx_size tuint)
                (Esizeof (Tstruct _sha512_state_st noattr) tuint)))))))))
|}.

Definition f_md5_sha1_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_md_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_ctx, (tptr (Tstruct __2975 noattr))) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _ctx
    (Efield
      (Ederef (Etempvar _md_ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _MD5_Init (Tfunction
                        (Tcons (tptr (Tstruct _md5_state_st noattr)) Tnil)
                        tint cc_default))
      ((Eaddrof
         (Efield
           (Ederef (Etempvar _ctx (tptr (Tstruct __2975 noattr)))
             (Tstruct __2975 noattr)) _md5 (Tstruct _md5_state_st noattr))
         (tptr (Tstruct _md5_state_st noattr))) :: nil))
    (Sifthenelse (Etempvar _t'1 tint)
      (Ssequence
        (Scall (Some _t'3)
          (Evar _SHA1_Init (Tfunction
                             (Tcons (tptr (Tstruct _sha_state_st noattr))
                               Tnil) tint cc_default))
          ((Eaddrof
             (Efield
               (Ederef (Etempvar _ctx (tptr (Tstruct __2975 noattr)))
                 (Tstruct __2975 noattr)) _sha1
               (Tstruct _sha_state_st noattr))
             (tptr (Tstruct _sha_state_st noattr))) :: nil))
        (Sset _t'2 (Ecast (Etempvar _t'3 tint) tbool)))
      (Sset _t'2 (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_md5_sha1_update := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_md_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_data, (tptr tvoid)) :: (_count, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_ctx, (tptr (Tstruct __2975 noattr))) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _ctx
    (Efield
      (Ederef (Etempvar _md_ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _MD5_Update (Tfunction
                          (Tcons (tptr (Tstruct _md5_state_st noattr))
                            (Tcons (tptr tvoid) (Tcons tuint Tnil))) tint
                          cc_default))
      ((Eaddrof
         (Efield
           (Ederef (Etempvar _ctx (tptr (Tstruct __2975 noattr)))
             (Tstruct __2975 noattr)) _md5 (Tstruct _md5_state_st noattr))
         (tptr (Tstruct _md5_state_st noattr))) ::
       (Etempvar _data (tptr tvoid)) :: (Etempvar _count tuint) :: nil))
    (Sifthenelse (Etempvar _t'1 tint)
      (Ssequence
        (Scall (Some _t'3)
          (Evar _SHA1_Update (Tfunction
                               (Tcons (tptr (Tstruct _sha_state_st noattr))
                                 (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                               tint cc_default))
          ((Eaddrof
             (Efield
               (Ederef (Etempvar _ctx (tptr (Tstruct __2975 noattr)))
                 (Tstruct __2975 noattr)) _sha1
               (Tstruct _sha_state_st noattr))
             (tptr (Tstruct _sha_state_st noattr))) ::
           (Etempvar _data (tptr tvoid)) :: (Etempvar _count tuint) :: nil))
        (Sset _t'2 (Ecast (Etempvar _t'3 tint) tbool)))
      (Sset _t'2 (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_md5_sha1_final := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_md_ctx, (tptr (Tstruct _env_md_ctx_st noattr))) ::
                (_out, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_ctx, (tptr (Tstruct __2975 noattr))) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _ctx
    (Efield
      (Ederef (Etempvar _md_ctx (tptr (Tstruct _env_md_ctx_st noattr)))
        (Tstruct _env_md_ctx_st noattr)) _md_data (tptr tvoid)))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _MD5_Final (Tfunction
                         (Tcons (tptr tuchar)
                           (Tcons (tptr (Tstruct _md5_state_st noattr)) Tnil))
                         tint cc_default))
      ((Etempvar _out (tptr tuchar)) ::
       (Eaddrof
         (Efield
           (Ederef (Etempvar _ctx (tptr (Tstruct __2975 noattr)))
             (Tstruct __2975 noattr)) _md5 (Tstruct _md5_state_st noattr))
         (tptr (Tstruct _md5_state_st noattr))) :: nil))
    (Sifthenelse (Etempvar _t'1 tint)
      (Ssequence
        (Scall (Some _t'3)
          (Evar _SHA1_Final (Tfunction
                              (Tcons (tptr tuchar)
                                (Tcons (tptr (Tstruct _sha_state_st noattr))
                                  Tnil)) tint cc_default))
          ((Ebinop Oadd (Etempvar _out (tptr tuchar))
             (Econst_int (Int.repr 16) tint) (tptr tuchar)) ::
           (Eaddrof
             (Efield
               (Ederef (Etempvar _ctx (tptr (Tstruct __2975 noattr)))
                 (Tstruct __2975 noattr)) _sha1
               (Tstruct _sha_state_st noattr))
             (tptr (Tstruct _sha_state_st noattr))) :: nil))
        (Sset _t'2 (Ecast (Etempvar _t'3 tint) tbool)))
      (Sset _t'2 (Econst_int (Int.repr 0) tint)))))
|}.

Definition v_EVP_md5_sha1_storage := {|
  gvar_info := (Tstruct _env_md_st noattr);
  gvar_init := (Init_space 32 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_EVP_md5_sha1_storage_bss_get := {|
  fn_return := (tptr (Tstruct _env_md_st noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eaddrof
                 (Evar _EVP_md5_sha1_storage (Tstruct _env_md_st noattr))
                 (tptr (Tstruct _env_md_st noattr)))))
|}.

Definition v_EVP_md5_sha1_once := {|
  gvar_info := tuint;
  gvar_init := (Init_int32 (Int.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_EVP_md5_sha1_once_bss_get := {|
  fn_return := (tptr tuint);
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eaddrof (Evar _EVP_md5_sha1_once tuint) (tptr tuint))))
|}.

Definition f_EVP_md5_sha1_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'1, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _EVP_md5_sha1_storage_bss_get (Tfunction Tnil
                                          (tptr (Tstruct _env_md_st noattr))
                                          cc_default)) nil)
  (Scall None
    (Evar _EVP_md5_sha1_do_init (Tfunction
                                  (Tcons (tptr (Tstruct _env_md_st noattr))
                                    Tnil) tvoid cc_default))
    ((Etempvar _t'1 (tptr (Tstruct _env_md_st noattr))) :: nil)))
|}.

Definition f_EVP_md5_sha1 := {|
  fn_return := (tptr (Tstruct _env_md_st noattr));
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'2, (tptr (Tstruct _env_md_st noattr))) ::
               (_t'1, (tptr tuint)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _EVP_md5_sha1_once_bss_get (Tfunction Tnil (tptr tuint)
                                         cc_default)) nil)
    (Scall None
      (Evar _CRYPTO_once (Tfunction
                           (Tcons (tptr tuint)
                             (Tcons (tptr (Tfunction Tnil tvoid cc_default))
                               Tnil)) tvoid cc_default))
      ((Etempvar _t'1 (tptr tuint)) ::
       (Evar _EVP_md5_sha1_init (Tfunction Tnil tvoid cc_default)) :: nil)))
  (Ssequence
    (Scall (Some _t'2)
      (Evar _EVP_md5_sha1_storage_bss_get (Tfunction Tnil
                                            (tptr (Tstruct _env_md_st noattr))
                                            cc_default)) nil)
    (Sreturn (Some (Ecast (Etempvar _t'2 (tptr (Tstruct _env_md_st noattr)))
                     (tptr (Tstruct _env_md_st noattr)))))))
|}.

Definition f_EVP_md5_sha1_do_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr (Tstruct _env_md_st noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
        (Tstruct _env_md_st noattr)) _type tint)
    (Econst_int (Int.repr 114) tint))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
          (Tstruct _env_md_st noattr)) _md_size tuint)
      (Ebinop Oadd (Econst_int (Int.repr 16) tint)
        (Econst_int (Int.repr 20) tint) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
            (Tstruct _env_md_st noattr)) _flags tuint)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
              (Tstruct _env_md_st noattr)) _init
            (tptr (Tfunction
                    (Tcons (tptr (Tstruct _env_md_ctx_st noattr)) Tnil) tvoid
                    cc_default)))
          (Evar _md5_sha1_init (Tfunction
                                 (Tcons
                                   (tptr (Tstruct _env_md_ctx_st noattr))
                                   Tnil) tvoid cc_default)))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                (Tstruct _env_md_st noattr)) _update
              (tptr (Tfunction
                      (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                        (Tcons (tptr tvoid) (Tcons tuint Tnil))) tvoid
                      cc_default)))
            (Evar _md5_sha1_update (Tfunction
                                     (Tcons
                                       (tptr (Tstruct _env_md_ctx_st noattr))
                                       (Tcons (tptr tvoid)
                                         (Tcons tuint Tnil))) tvoid
                                     cc_default)))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                  (Tstruct _env_md_st noattr)) _final
                (tptr (Tfunction
                        (Tcons (tptr (Tstruct _env_md_ctx_st noattr))
                          (Tcons (tptr tuchar) Tnil)) tvoid cc_default)))
              (Evar _md5_sha1_final (Tfunction
                                      (Tcons
                                        (tptr (Tstruct _env_md_ctx_st noattr))
                                        (Tcons (tptr tuchar) Tnil)) tvoid
                                      cc_default)))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                    (Tstruct _env_md_st noattr)) _block_size tuint)
                (Econst_int (Int.repr 64) tint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _out (tptr (Tstruct _env_md_st noattr)))
                    (Tstruct _env_md_st noattr)) _ctx_size tuint)
                (Esizeof (Tstruct __2975 noattr) tuint)))))))))
|}.

Definition composites : list composite_definition :=
(Composite _env_md_ctx_st Struct
   ((_digest, (tptr (Tstruct _env_md_st noattr))) ::
    (_md_data, (tptr tvoid)) ::
    (_pctx, (tptr (Tstruct _evp_pkey_ctx_st noattr))) ::
    (_pctx_ops, (tptr (Tstruct _evp_md_pctx_ops noattr))) :: nil)
   noattr ::
 Composite _md4_state_st Struct
   ((_h, (tarray tuint 4)) :: (_Nl, tuint) :: (_Nh, tuint) ::
    (_data, (tarray tuchar 64)) :: (_num, tuint) :: nil)
   noattr ::
 Composite _md5_state_st Struct
   ((_h, (tarray tuint 4)) :: (_Nl, tuint) :: (_Nh, tuint) ::
    (_data, (tarray tuchar 64)) :: (_num, tuint) :: nil)
   noattr ::
 Composite __2217 Struct
   ((_h0, tuint) :: (_h1, tuint) :: (_h2, tuint) :: (_h3, tuint) ::
    (_h4, tuint) :: nil)
   noattr ::
 Composite __2216 Union
   ((_h, (tarray tuint 5)) :: (132%positive, (Tstruct __2217 noattr)) :: nil)
   noattr ::
 Composite _sha_state_st Struct
   ((132%positive, (Tunion __2216 noattr)) :: (_Nl, tuint) :: (_Nh, tuint) ::
    (_data, (tarray tuchar 64)) :: (_num, tuint) :: nil)
   noattr ::
 Composite _sha256_state_st Struct
   ((_h, (tarray tuint 8)) :: (_Nl, tuint) :: (_Nh, tuint) ::
    (_data, (tarray tuchar 64)) :: (_num, tuint) :: (_md_len, tuint) :: nil)
   noattr ::
 Composite __2279 Union
   ((_d, (tarray tulong 16)) :: (_p, (tarray tuchar 128)) :: nil)
   noattr ::
 Composite _sha512_state_st Struct
   ((_h, (tarray tulong 8)) :: (_Nl, tulong) :: (_Nh, tulong) ::
    (_u, (Tunion __2279 noattr)) :: (_num, tuint) :: (_md_len, tuint) :: nil)
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
   noattr ::
 Composite __2975 Struct
   ((_md5, (Tstruct _md5_state_st noattr)) ::
    (_sha1, (Tstruct _sha_state_st noattr)) :: nil)
   noattr :: nil).

Definition global_definitions :=
((___builtin_fabs,
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
 (_MD4_Init,
   Gfun(External (EF_external "MD4_Init"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _md4_state_st noattr)) Tnil) tint cc_default)) ::
 (_MD4_Update,
   Gfun(External (EF_external "MD4_Update"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _md4_state_st noattr))
       (Tcons (tptr tvoid) (Tcons tuint Tnil))) tint cc_default)) ::
 (_MD4_Final,
   Gfun(External (EF_external "MD4_Final"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default))
     (Tcons (tptr tuchar) (Tcons (tptr (Tstruct _md4_state_st noattr)) Tnil))
     tint cc_default)) ::
 (_MD5_Init,
   Gfun(External (EF_external "MD5_Init"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _md5_state_st noattr)) Tnil) tint cc_default)) ::
 (_MD5_Update,
   Gfun(External (EF_external "MD5_Update"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _md5_state_st noattr))
       (Tcons (tptr tvoid) (Tcons tuint Tnil))) tint cc_default)) ::
 (_MD5_Final,
   Gfun(External (EF_external "MD5_Final"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default))
     (Tcons (tptr tuchar) (Tcons (tptr (Tstruct _md5_state_st noattr)) Tnil))
     tint cc_default)) ::
 (_SHA1_Init,
   Gfun(External (EF_external "SHA1_Init"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _sha_state_st noattr)) Tnil) tint cc_default)) ::
 (_SHA1_Update,
   Gfun(External (EF_external "SHA1_Update"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _sha_state_st noattr))
       (Tcons (tptr tvoid) (Tcons tuint Tnil))) tint cc_default)) ::
 (_SHA1_Final,
   Gfun(External (EF_external "SHA1_Final"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default))
     (Tcons (tptr tuchar) (Tcons (tptr (Tstruct _sha_state_st noattr)) Tnil))
     tint cc_default)) ::
 (_SHA224_Init,
   Gfun(External (EF_external "SHA224_Init"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _sha256_state_st noattr)) Tnil) tint cc_default)) ::
 (_SHA224_Update,
   Gfun(External (EF_external "SHA224_Update"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _sha256_state_st noattr))
       (Tcons (tptr tvoid) (Tcons tuint Tnil))) tint cc_default)) ::
 (_SHA224_Final,
   Gfun(External (EF_external "SHA224_Final"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default))
     (Tcons (tptr tuchar)
       (Tcons (tptr (Tstruct _sha256_state_st noattr)) Tnil)) tint
     cc_default)) ::
 (_SHA256_Init,
   Gfun(External (EF_external "SHA256_Init"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _sha256_state_st noattr)) Tnil) tint cc_default)) ::
 (_SHA256_Update,
   Gfun(External (EF_external "SHA256_Update"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _sha256_state_st noattr))
       (Tcons (tptr tvoid) (Tcons tuint Tnil))) tint cc_default)) ::
 (_SHA256_Final,
   Gfun(External (EF_external "SHA256_Final"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default))
     (Tcons (tptr tuchar)
       (Tcons (tptr (Tstruct _sha256_state_st noattr)) Tnil)) tint
     cc_default)) ::
 (_SHA384_Init,
   Gfun(External (EF_external "SHA384_Init"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _sha512_state_st noattr)) Tnil) tint cc_default)) ::
 (_SHA384_Update,
   Gfun(External (EF_external "SHA384_Update"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _sha512_state_st noattr))
       (Tcons (tptr tvoid) (Tcons tuint Tnil))) tint cc_default)) ::
 (_SHA384_Final,
   Gfun(External (EF_external "SHA384_Final"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default))
     (Tcons (tptr tuchar)
       (Tcons (tptr (Tstruct _sha512_state_st noattr)) Tnil)) tint
     cc_default)) ::
 (_SHA512_Init,
   Gfun(External (EF_external "SHA512_Init"
                   (mksignature (AST.Tint :: nil) (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _sha512_state_st noattr)) Tnil) tint cc_default)) ::
 (_SHA512_Update,
   Gfun(External (EF_external "SHA512_Update"
                   (mksignature (AST.Tint :: AST.Tint :: AST.Tint :: nil)
                     (Some AST.Tint) cc_default))
     (Tcons (tptr (Tstruct _sha512_state_st noattr))
       (Tcons (tptr tvoid) (Tcons tuint Tnil))) tint cc_default)) ::
 (_SHA512_Final,
   Gfun(External (EF_external "SHA512_Final"
                   (mksignature (AST.Tint :: AST.Tint :: nil) (Some AST.Tint)
                     cc_default))
     (Tcons (tptr tuchar)
       (Tcons (tptr (Tstruct _sha512_state_st noattr)) Tnil)) tint
     cc_default)) ::
 (_CRYPTO_once,
   Gfun(External (EF_external "CRYPTO_once"
                   (mksignature (AST.Tint :: AST.Tint :: nil) None
                     cc_default))
     (Tcons (tptr tuint)
       (Tcons (tptr (Tfunction Tnil tvoid cc_default)) Tnil)) tvoid
     cc_default)) :: (_md4_init, Gfun(Internal f_md4_init)) ::
 (_md4_update, Gfun(Internal f_md4_update)) ::
 (_md4_final, Gfun(Internal f_md4_final)) ::
 (_EVP_md4_storage, Gvar v_EVP_md4_storage) ::
 (_EVP_md4_storage_bss_get, Gfun(Internal f_EVP_md4_storage_bss_get)) ::
 (_EVP_md4_once, Gvar v_EVP_md4_once) ::
 (_EVP_md4_once_bss_get, Gfun(Internal f_EVP_md4_once_bss_get)) ::
 (_EVP_md4_init, Gfun(Internal f_EVP_md4_init)) ::
 (_EVP_md4, Gfun(Internal f_EVP_md4)) ::
 (_EVP_md4_do_init, Gfun(Internal f_EVP_md4_do_init)) ::
 (_md5_init, Gfun(Internal f_md5_init)) ::
 (_md5_update, Gfun(Internal f_md5_update)) ::
 (_md5_final, Gfun(Internal f_md5_final)) ::
 (_EVP_md5_storage, Gvar v_EVP_md5_storage) ::
 (_EVP_md5_storage_bss_get, Gfun(Internal f_EVP_md5_storage_bss_get)) ::
 (_EVP_md5_once, Gvar v_EVP_md5_once) ::
 (_EVP_md5_once_bss_get, Gfun(Internal f_EVP_md5_once_bss_get)) ::
 (_EVP_md5_init, Gfun(Internal f_EVP_md5_init)) ::
 (_EVP_md5, Gfun(Internal f_EVP_md5)) ::
 (_EVP_md5_do_init, Gfun(Internal f_EVP_md5_do_init)) ::
 (_sha1_init, Gfun(Internal f_sha1_init)) ::
 (_sha1_update, Gfun(Internal f_sha1_update)) ::
 (_sha1_final, Gfun(Internal f_sha1_final)) ::
 (_EVP_sha1_storage, Gvar v_EVP_sha1_storage) ::
 (_EVP_sha1_storage_bss_get, Gfun(Internal f_EVP_sha1_storage_bss_get)) ::
 (_EVP_sha1_once, Gvar v_EVP_sha1_once) ::
 (_EVP_sha1_once_bss_get, Gfun(Internal f_EVP_sha1_once_bss_get)) ::
 (_EVP_sha1_init, Gfun(Internal f_EVP_sha1_init)) ::
 (_EVP_sha1, Gfun(Internal f_EVP_sha1)) ::
 (_EVP_sha1_do_init, Gfun(Internal f_EVP_sha1_do_init)) ::
 (_sha224_init, Gfun(Internal f_sha224_init)) ::
 (_sha224_update, Gfun(Internal f_sha224_update)) ::
 (_sha224_final, Gfun(Internal f_sha224_final)) ::
 (_EVP_sha224_storage, Gvar v_EVP_sha224_storage) ::
 (_EVP_sha224_storage_bss_get, Gfun(Internal f_EVP_sha224_storage_bss_get)) ::
 (_EVP_sha224_once, Gvar v_EVP_sha224_once) ::
 (_EVP_sha224_once_bss_get, Gfun(Internal f_EVP_sha224_once_bss_get)) ::
 (_EVP_sha224_init, Gfun(Internal f_EVP_sha224_init)) ::
 (_EVP_sha224, Gfun(Internal f_EVP_sha224)) ::
 (_EVP_sha224_do_init, Gfun(Internal f_EVP_sha224_do_init)) ::
 (_sha256_init, Gfun(Internal f_sha256_init)) ::
 (_sha256_update, Gfun(Internal f_sha256_update)) ::
 (_sha256_final, Gfun(Internal f_sha256_final)) ::
 (_EVP_sha256_storage, Gvar v_EVP_sha256_storage) ::
 (_EVP_sha256_storage_bss_get, Gfun(Internal f_EVP_sha256_storage_bss_get)) ::
 (_EVP_sha256_once, Gvar v_EVP_sha256_once) ::
 (_EVP_sha256_once_bss_get, Gfun(Internal f_EVP_sha256_once_bss_get)) ::
 (_EVP_sha256_init, Gfun(Internal f_EVP_sha256_init)) ::
 (_EVP_sha256, Gfun(Internal f_EVP_sha256)) ::
 (_EVP_sha256_do_init, Gfun(Internal f_EVP_sha256_do_init)) ::
 (_sha384_init, Gfun(Internal f_sha384_init)) ::
 (_sha384_update, Gfun(Internal f_sha384_update)) ::
 (_sha384_final, Gfun(Internal f_sha384_final)) ::
 (_EVP_sha384_storage, Gvar v_EVP_sha384_storage) ::
 (_EVP_sha384_storage_bss_get, Gfun(Internal f_EVP_sha384_storage_bss_get)) ::
 (_EVP_sha384_once, Gvar v_EVP_sha384_once) ::
 (_EVP_sha384_once_bss_get, Gfun(Internal f_EVP_sha384_once_bss_get)) ::
 (_EVP_sha384_init, Gfun(Internal f_EVP_sha384_init)) ::
 (_EVP_sha384, Gfun(Internal f_EVP_sha384)) ::
 (_EVP_sha384_do_init, Gfun(Internal f_EVP_sha384_do_init)) ::
 (_sha512_init, Gfun(Internal f_sha512_init)) ::
 (_sha512_update, Gfun(Internal f_sha512_update)) ::
 (_sha512_final, Gfun(Internal f_sha512_final)) ::
 (_EVP_sha512_storage, Gvar v_EVP_sha512_storage) ::
 (_EVP_sha512_storage_bss_get, Gfun(Internal f_EVP_sha512_storage_bss_get)) ::
 (_EVP_sha512_once, Gvar v_EVP_sha512_once) ::
 (_EVP_sha512_once_bss_get, Gfun(Internal f_EVP_sha512_once_bss_get)) ::
 (_EVP_sha512_init, Gfun(Internal f_EVP_sha512_init)) ::
 (_EVP_sha512, Gfun(Internal f_EVP_sha512)) ::
 (_EVP_sha512_do_init, Gfun(Internal f_EVP_sha512_do_init)) ::
 (_md5_sha1_init, Gfun(Internal f_md5_sha1_init)) ::
 (_md5_sha1_update, Gfun(Internal f_md5_sha1_update)) ::
 (_md5_sha1_final, Gfun(Internal f_md5_sha1_final)) ::
 (_EVP_md5_sha1_storage, Gvar v_EVP_md5_sha1_storage) ::
 (_EVP_md5_sha1_storage_bss_get, Gfun(Internal f_EVP_md5_sha1_storage_bss_get)) ::
 (_EVP_md5_sha1_once, Gvar v_EVP_md5_sha1_once) ::
 (_EVP_md5_sha1_once_bss_get, Gfun(Internal f_EVP_md5_sha1_once_bss_get)) ::
 (_EVP_md5_sha1_init, Gfun(Internal f_EVP_md5_sha1_init)) ::
 (_EVP_md5_sha1, Gfun(Internal f_EVP_md5_sha1)) ::
 (_EVP_md5_sha1_do_init, Gfun(Internal f_EVP_md5_sha1_do_init)) :: nil).

Definition public_idents :=
(_EVP_md5_sha1 :: _EVP_sha512 :: _EVP_sha384 :: _EVP_sha256 :: _EVP_sha224 ::
 _EVP_sha1 :: _EVP_md5 :: _EVP_md4 :: _CRYPTO_once :: _SHA512_Final ::
 _SHA512_Update :: _SHA512_Init :: _SHA384_Final :: _SHA384_Update ::
 _SHA384_Init :: _SHA256_Final :: _SHA256_Update :: _SHA256_Init ::
 _SHA224_Final :: _SHA224_Update :: _SHA224_Init :: _SHA1_Final ::
 _SHA1_Update :: _SHA1_Init :: _MD5_Final :: _MD5_Update :: _MD5_Init ::
 _MD4_Final :: _MD4_Update :: _MD4_Init :: ___builtin_debug ::
 ___builtin_nop :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_fsqrt :: ___builtin_ctzll ::
 ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll :: ___builtin_clzl ::
 ___builtin_clz :: ___builtin_bswap16 :: ___builtin_bswap32 ::
 ___builtin_bswap64 :: ___builtin_bswap :: ___i64_umulh :: ___i64_smulh ::
 ___i64_sar :: ___i64_shr :: ___i64_shl :: ___i64_umod :: ___i64_smod ::
 ___i64_udiv :: ___i64_sdiv :: ___i64_utof :: ___i64_stof :: ___i64_utod ::
 ___i64_stod :: ___i64_dtou :: ___i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_memcpy_aligned :: ___builtin_fabs :: nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


