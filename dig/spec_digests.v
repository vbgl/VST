Require Import floyd.proofauto.
Require Import floyd.library.
Require Import dig.digests.
Require Import dig.digest.

Lemma func_ptr'_isptr' v f: (func_ptr' f v) = ((!! isptr v) && func_ptr' f v).
Proof. apply pred_ext; entailer!. Qed.

Lemma writable_nonidentity sh (W:writable_share sh): sepalg.nonidentity sh.
Proof. apply readable_nonidentity. apply writable_readable; trivial. Qed.

Lemma semax_orp {cs Espec Delta P1 P2 Q c}
  (HR1: @semax cs Espec Delta P1 c Q)
  (HR2: @semax cs Espec Delta P2 c Q):
  @semax cs Espec Delta (P1 || P2) c Q.
Proof.
 eapply semax_pre with (P':=EX x:bool, if x then P1 else P2).
+ old_go_lower. apply orp_left; [Exists true | Exists false]; entailer!.
+ Intros b. destruct b; trivial.
Qed.

Lemma semax_orp_SEPx (cs : compspecs) (Espec : OracleKind)
      (Delta : tycontext) (P : list Prop) (Q : list localdef)
      (R1 R2 : mpred) (R:list mpred) (T : ret_assert) (c : statement)
  (HR1 : semax Delta
         (PROPx P (LOCALx Q (SEPx (cons R1 R)))) c T)
  (HR2 : semax Delta
         (PROPx P (LOCALx Q (SEPx (cons R2 R)))) c T):
semax Delta
  (PROPx P (LOCALx Q (SEPx (cons (orp R1 R2) R)))) c T.
Proof.
 eapply semax_pre; [| apply (semax_orp HR1 HR2)].
 old_go_lower.
 rewrite distrib_orp_sepcon. normalize. 
 (* destruct Q; solve 
   [ apply orp_left; [apply orp_right1| apply orp_right2]; entailer! ].*)
Qed.
Lemma semax_orp_SEPnil cs Espec Delta P Q R1 R2 T c
  (HR1: @semax cs Espec Delta (PROP (P) LOCAL (Q) SEP (R1)) c T)
  (HR2: @semax cs Espec Delta (PROP (P) LOCAL (Q) SEP (R2)) c T):
  @semax cs Espec Delta (PROP (P) LOCAL (Q) SEP (R1 || R2)) c T.
Proof. apply semax_orp_SEPx; trivial. Qed.
Lemma semax_orp_SEP cs Espec Delta P Q R1 R2 R T c
  (HR1: @semax cs Espec Delta (PROP (P) LOCAL (Q) SEP (R1; R)) c T)
  (HR2: @semax cs Espec Delta (PROP (P) LOCAL (Q) SEP (R2; R)) c T):
  @semax cs Espec Delta (PROP (P) LOCAL (Q) SEP ((R1 || R2); R)) c T.
Proof. apply semax_orp_SEPx; trivial. Qed.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import dig.digest_model.

(*From openssl_nid.h*)
Definition NID_of_DigestNID (NID:DigestNID):Z:=
match NID with
   NID_md5 => 4
 | NID_sha1 => 64
 | NID_sha224 => 675
 | NID_sha256 => 672
 | NID_sha384 => 673
 | NID_sha512 => 674
 | NID_md5_sha1 => 114
 | NID_dsaWithSHA => 66
 | NID_dsaWithSHA1 => 113
 | NID_ecdsa_with_SHA1 => 416
 | NID_md5WithRSAEncryption => 8
 | NID_sha1WithRSAEncryption => 65
 | NID_sha224WithRSAEncryption => 671
 | NID_sha256WithRSAEncryption => 668
 | NID_sha384WithRSAEncryption => 669
 | NID_sha512WithRSAEncryption => 670
end.

Parameter init_spec_of_NID: DigestNID -> funspec. (*todo: fill in spec*)
Parameter update_spec_of_NID:DigestNID -> funspec. (*todo: fill in spec*)
Parameter final_spec_of_NID: DigestNID -> funspec. (*todo: fill in spec*)

Definition matchEVP_MD_record (R:EVP_MD_record) (vals: reptype (Tstruct _env_md_st noattr)): mpred :=
match vals with
  ((type, (mdsize, (flags, (ini, (upd, (fin, (blocksize, ctxsize)))))))%type) =>
  !! (type = Vint (Int.repr (NID_of_DigestNID (EVP_MD_rec_type R))) /\
      mdsize = Vint (Int.repr (EVP_MD_rec_md_size R)) /\
      flags = Vint (Int.repr (EVP_MD_rec_flags R)) /\
      blocksize = Vint (Int.repr (EVP_MD_rec_block_size R )) /\
      ctxsize = Vint (Int.repr (EVP_MD_rec_ctx_size R )))
   && (func_ptr' (init_spec_of_NID (EVP_MD_rec_type R)) ini *
       func_ptr' (update_spec_of_NID (EVP_MD_rec_type R)) upd *
       func_ptr' (final_spec_of_NID (EVP_MD_rec_type R)) fin)
end.
 
Definition EVP_MD_rep (R:EVP_MD_record) (p:val):mpred :=
  EX sh:_, EX vals :_,
  !!readable_share sh && 
  (matchEVP_MD_record R vals * data_at sh (Tstruct _env_md_st noattr) vals p).


Lemma EVP_MD_rep_isptr R p:  EVP_MD_rep R p |-- !!(isptr p).
Proof. unfold EVP_MD_rep. Intros sh vals. entailer!. Qed.

Lemma EVP_MD_rep_isptr' R p:  EVP_MD_rep R p = (!!(isptr p) && EVP_MD_rep R p).
Proof. apply pred_ext; entailer. apply EVP_MD_rep_isptr. Qed. 

Lemma EVP_MD_rep_validptr R p:  EVP_MD_rep R p |-- valid_pointer p.
Proof. unfold EVP_MD_rep. Intros sh vals. entailer!. Qed.

Definition EVP_MD_type_SPEC := DECLARE _EVP_MD_type
  WITH md:val, R:EVP_MD_record
  PRE [ _md OF (tptr (Tstruct _env_md_st noattr)) ]
      PROP ()
      LOCAL (temp _md md)
      SEP (EVP_MD_rep R md)
  POST [tint]
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr (NID_of_DigestNID (EVP_MD_rec_type R)))))
       SEP (EVP_MD_rep R md).

Definition EVP_MD_flags_SPEC := DECLARE _EVP_MD_flags
  WITH md:val, R:EVP_MD_record
  PRE [ _md OF (tptr (Tstruct _env_md_st noattr)) ]
      PROP ()
      LOCAL (temp _md md)
      SEP (EVP_MD_rep R md)
  POST [tuint]
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr (EVP_MD_rec_flags R))))
       SEP (EVP_MD_rep R md).

Definition EVP_MD_size_SPEC := DECLARE _EVP_MD_size
  WITH md:val, R:EVP_MD_record
  PRE [ _md OF (tptr (Tstruct _env_md_st noattr)) ]
      PROP ()
      LOCAL (temp _md md)
      SEP (EVP_MD_rep R md)
  POST [tuint]
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr (EVP_MD_rec_md_size R))))
       SEP (EVP_MD_rep R md).

Definition EVP_MD_block_size_SPEC := DECLARE _EVP_MD_block_size
  WITH md:val, R:EVP_MD_record
  PRE [ _md OF (tptr (Tstruct _env_md_st noattr)) ]
      PROP ()
      LOCAL (temp _md md)
      SEP (EVP_MD_rep R md)
  POST [tuint]
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr (EVP_MD_rec_block_size R))))
       SEP (EVP_MD_rep R md).

Definition Gprog_EVPMD : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [EVP_MD_type_SPEC; EVP_MD_flags_SPEC; EVP_MD_size_SPEC; EVP_MD_block_size_SPEC].


Lemma body_EVP_MD_type: semax_body Vprog Gprog_EVPMD f_EVP_MD_type EVP_MD_type_SPEC. 
Proof.
  start_function.  
  unfold EVP_MD_rep. Intros sh vals; rename H into Rsh. 
  destruct vals as (type, (mdsize, (flags, (ini, (upd, (fin, (blocksize, ctxsize))))))); simpl in *.
  Intros. forward. forward.  
  Exists sh (Vint (Int.repr (NID_of_DigestNID (EVP_MD_rec_type R))),
       (Vint (Int.repr (EVP_MD_rec_md_size R)),
       (Vint (Int.repr (EVP_MD_rec_flags R)),
       (ini,
       (upd,
       (fin,
       (Vint (Int.repr (EVP_MD_rec_block_size R)),
       Vint (Int.repr (EVP_MD_rec_ctx_size R))))))))). 
  simpl. entailer!.
Qed. 

Lemma body_EVP_MD_flags: semax_body Vprog Gprog_EVPMD f_EVP_MD_flags EVP_MD_flags_SPEC. 
Proof.
  start_function.  
  unfold EVP_MD_rep. Intros sh vals; rename H into Rsh. 
  destruct vals as (type, (mdsize, (flags, (ini, (upd, (fin, (blocksize, ctxsize))))))); simpl in *.
  Intros. forward. forward.  
  Exists sh (Vint (Int.repr (NID_of_DigestNID (EVP_MD_rec_type R))),
       (Vint (Int.repr (EVP_MD_rec_md_size R)),
       (Vint (Int.repr (EVP_MD_rec_flags R)),
       (ini,
       (upd,
       (fin,
       (Vint (Int.repr (EVP_MD_rec_block_size R)),
       Vint (Int.repr (EVP_MD_rec_ctx_size R))))))))). 
  simpl. entailer!.
Qed. 

Lemma body_EVP_MD_size: semax_body Vprog Gprog_EVPMD f_EVP_MD_size EVP_MD_size_SPEC. 
Proof.
  start_function.  
  unfold EVP_MD_rep. Intros sh vals; rename H into Rsh. 
  destruct vals as (type, (mdsize, (flags, (ini, (upd, (fin, (blocksize, ctxsize))))))); simpl in *.
  Intros. forward. forward.  
  Exists sh (Vint (Int.repr (NID_of_DigestNID (EVP_MD_rec_type R))),
       (Vint (Int.repr (EVP_MD_rec_md_size R)),
       (Vint (Int.repr (EVP_MD_rec_flags R)),
       (ini,
       (upd,
       (fin,
       (Vint (Int.repr (EVP_MD_rec_block_size R)),
       Vint (Int.repr (EVP_MD_rec_ctx_size R))))))))). 
  simpl. entailer!.
Qed. 

Lemma body_EVP_MD_block_size: semax_body Vprog Gprog_EVPMD f_EVP_MD_block_size EVP_MD_block_size_SPEC. 
Proof.
  start_function.  
  unfold EVP_MD_rep. Intros sh vals; rename H into Rsh. 
  destruct vals as (type, (mdsize, (flags, (ini, (upd, (fin, (blocksize, ctxsize))))))); simpl in *.
  Intros. forward. forward.  
  Exists sh (Vint (Int.repr (NID_of_DigestNID (EVP_MD_rec_type R))),
       (Vint (Int.repr (EVP_MD_rec_md_size R)),
       (Vint (Int.repr (EVP_MD_rec_flags R)),
       (ini,
       (upd,
       (fin,
       (Vint (Int.repr (EVP_MD_rec_block_size R)),
       Vint (Int.repr (EVP_MD_rec_ctx_size R))))))))). 
  simpl. entailer!.
Qed. 

(*Taken from spec_sha TODO: adapt to OPENSSL's code, and verify the body (code is included in digest.v)*)
Definition OPENSSL_memcpy_SPEC := DECLARE _OPENSSL_memcpy
   WITH sh : share*share, p: val, q: val, n: Z, contents: list int
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid, 3%positive OF tuint ]
       PROP (readable_share (fst sh); writable_share (snd sh); 0 <= n <= Int.max_unsigned)
       LOCAL (temp 1%positive p; temp 2%positive q; temp 3%positive (Vint (Int.repr n)))
       SEP (data_at (fst sh) (tarray tuchar n) (map Vint contents) q;
              memory_block (snd sh) n p)
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp p)
       SEP(data_at (fst sh) (tarray tuchar n) (map Vint contents) q;
             data_at (snd sh) (tarray tuchar n) (map Vint contents) p).

Inductive memsetCase :=
  memsetNull: memsetCase
| memsetNonnull: share -> memsetCase.

(*Taken from spec_sha; indeed, it seems p==null yields undef behavior in C11 standard*)
Definition memset_spec :=
  DECLARE _memset
   WITH sh : share, p: val, n: Z, c: int
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tint, 3%positive OF tuint ]
       PROP (writable_share sh; 0 <= n <= Int.max_unsigned)
       LOCAL (temp 1%positive p; temp 2%positive (Vint c);
                   temp 3%positive (Vint (Int.repr n)))
       SEP (memory_block sh n p)
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp p)
       SEP(data_at sh (tarray tuchar n) (list_repeat (Z.to_nat n) (Vint c)) p).

Definition OPENSSL_memset_SPEC := DECLARE _OPENSSL_memset  
   WITH p: val, n: Z, c: int, case: memsetCase
   PRE [ _dst OF tptr tvoid, _c OF tint, _n OF tuint ]
       PROP ()
       LOCAL (temp _dst p; temp _c (Vint c); temp _n (Vint (Int.repr n)))
       SEP (match case with
            | memsetNull => !!(n=0) && emp
            | memsetNonnull sh => !!(writable_share sh /\ 0 < n <= Int.max_unsigned) 
                            && memory_block sh n p
            end)
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp p)
       SEP(match case with 
           | memsetNull => emp
           | memsetNonnull sh => data_at sh (tarray tuchar n) (list_repeat (Z.to_nat n) (Vint c)) p
           end).

Definition GprogMemset: funspecs := [OPENSSL_memset_SPEC; memset_spec].
Lemma body_OPENSSL_mmemset_SPEC: semax_body Vprog GprogMemset f_OPENSSL_memset OPENSSL_memset_SPEC.
Proof.
  start_function. destruct case; Intros; subst.
+ (*memsetNull*)
  forward_if (PROP ( False ) LOCAL () SEP ()); [ clear H; forward | inv H | normalize ].
+ (*memsetPtr*)
  forward_if (
    PROP ( )
    LOCAL (temp _dst p; temp _c (Vint c); temp _n (Vint (Int.repr n)))
    SEP (memory_block s n p)); [ omega | forward ; entailer! | ].
  forward_call (s,p,n,c); [ intuition | forward ].
Qed.

(**** Other functions called from digest.c but not equipped with function bodies in digest.v***) 
(*Taken from verif_bst's mallocN.  TODO: adapt to OPENSSL's code, and verify the body.
 Also: possibly, add TOKEN*)
Definition OPENSSL_malloc_SPEC := DECLARE _malloc
  WITH n: Z
  PRE [ 1%positive OF tuint] (*note: in verif_bst, it's a tint*)
     PROP (4 <= n <= Int.max_unsigned)
     LOCAL (temp 1%positive (Vint (Int.repr n)))
     SEP ()
  POST [ tptr tvoid ]
     EX v: val,
     PROP ()
     LOCAL (temp ret_temp v)
     SEP ((!!(v=nullval) && emp) || (!!(malloc_compatible n v) && memory_block Tsh n v)).

(*verif_bst has this:
Definition _free_SPEC := DECLARE _free
  WITH p : val , n : Z
  PRE [ 1%positive OF tptr tvoid , 2%positive OF tint]
     (* we should also require natural_align_compatible (eval_id 1) *)
      PROP() LOCAL (temp 1%positive p; temp 2%positive (Vint (Int.repr n)))
      SEP (memory_block Tsh n p)
  POST [ tvoid ]
    PROP () LOCAL () SEP ().*)
(*In C11 etc, can calling free(NULL) is ok*)
Definition OPENSSL_free_SPEC := DECLARE _free
  WITH p : val , n : Z
  PRE [ 1%positive OF tptr tvoid]
     (* we should also require natural_align_compatible (eval_id 1) *)
      PROP() LOCAL (temp 1%positive p)
      SEP ((!!(p=nullval)&&emp) || memory_block Tsh n p)
  POST [ tvoid ]
    PROP () LOCAL () SEP ().

(* Specification in mem.h: OPENSSL_cleanse zeros out |len| bytes of memory at |ptr|. 
                           This is similar to |memset_s| from C11.
   Our spec is essentially identical to the one of memset (with value 0)*)
Definition OPENSSL_cleanse_SPEC := DECLARE _OPENSSL_cleanse
  WITH p: val, sh : share, n: Z
  PRE [ 1%positive OF tptr tvoid , 2%positive OF tuint]
      PROP(writable_share sh; 0 <= n <= Int.max_unsigned) 
      LOCAL (temp 1%positive p; temp 2%positive (Vint (Int.repr n)))
      SEP (memory_block sh n p)
  POST [ tvoid ]
    PROP () LOCAL () 
    SEP (data_at sh (tarray tuchar n) (list_repeat (Z.to_nat n) (Vint Int.zero)) p).

Definition EVP_MD_CTX_init_SPEC := DECLARE _EVP_MD_CTX_init
   WITH ctx:val, sh:share, n:Z
   PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr) ]
       PROP (writable_share sh; n=sizeof (Tstruct _env_md_ctx_st noattr))
       LOCAL (temp _ctx ctx)
       SEP (data_at_ sh (Tstruct _env_md_ctx_st noattr) ctx)
   POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (data_at sh (tarray tuchar n) (list_repeat (Z.to_nat n) (Vint Int.zero)) ctx).

Definition EVP_MD_CTX_create_SPEC := DECLARE _EVP_MD_CTX_create
   WITH ctx:val
   PRE [ ]
       PROP ()
       LOCAL ( )
       SEP ()
   POST [ tptr (Tstruct _env_md_ctx_st noattr) ]
     EX ctx:val,
       PROP ()
       LOCAL (temp ret_temp ctx)
       SEP ((!!(ctx=nullval) && emp) || data_at_ Tsh (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr))) ctx).

Definition Gprog_EVPMDCTX_1 : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [EVP_MD_CTX_create_SPEC; EVP_MD_CTX_init_SPEC; OPENSSL_memset_SPEC; OPENSSL_malloc_SPEC].

Lemma body_EVP_MD_CTX_init: semax_body Vprog Gprog_EVPMDCTX_1 f_EVP_MD_CTX_init EVP_MD_CTX_init_SPEC.
Proof.
  start_function. simpl in *; subst.
  rewrite data_at__memory_block; simpl; Intros.
  forward_call (ctx, 16, Int.zero, memsetNonnull sh). entailer!.
  forward.
Qed. 

Lemma body_EVP_MD_CTX_create: semax_body Vprog Gprog_EVPMDCTX_1 f_EVP_MD_CTX_create EVP_MD_CTX_create_SPEC.
Proof.
  start_function. 
  forward_call (sizeof (Tstruct _env_md_ctx_st noattr)). 
    rewrite int_max_unsigned_eq; simpl; omega.
  Intros v. flatten_emp. 
  apply semax_orp_SEPx; Intros; subst.
+ forward_if (PROP ( )  LOCAL (temp _ctx (Vint Int.zero))  SEP ()).
  - simpl in H; contradiction.
  - forward. entailer!.
  - forward. Exists (Vint Int.zero). entailer!. apply orp_right1; trivial.
+ rewrite memory_block_data_at_ by (apply malloc_compatible_field_compatible; simpl; trivial; exists 2; reflexivity).
  forward_if (PROP ( ) LOCAL (temp _ctx v)  SEP (data_at_ Tsh (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr))) v)).
  - apply denote_tc_test_eq_split.
    apply data_at_valid_ptr. apply top_share_nonidentity. simpl; omega.
    apply valid_pointer_null.
  - forward_call (v, Tsh, sizeof (Tstruct _env_md_ctx_st noattr)). entailer!.
  - subst; rewrite data_at__isptr. normalize.
  - forward. Exists v. entailer!. apply orp_right2; trivial. 
Qed.


(****** Specs of the four Digest Operation Accessors. *******)
(*nonnull node*)
Definition EVP_MD_CTX_NNnode (sh:share) (vals:val*(val*(val*val))) (p:val):mpred :=
  match vals with (d, (mddata, (pctx, pctxops))) =>
  !!(is_pointer_or_null d /\ is_pointer_or_null mddata) &&
  data_at sh (Tstruct _env_md_ctx_st noattr) (d,(mddata,(pctx, pctxops))) p
  end.

Lemma EVP_MD_CTX_NNnode_isptr sh vals p:
  EVP_MD_CTX_NNnode sh vals p |-- !!(isptr p).
Proof.
  unfold EVP_MD_CTX_NNnode. destruct vals as [d [mdd [pc pcops]]]. normalize.
  rewrite data_at_isptr. entailer!.
Qed.
Lemma EVP_MD_CTX_NNnode_isptr' sh vals p:
  EVP_MD_CTX_NNnode sh vals p  = (!!(isptr p) &&  EVP_MD_CTX_NNnode sh vals p).
Proof.
  apply pred_ext; [ entailer; apply EVP_MD_CTX_NNnode_isptr | entailer!].
Qed.

(*a possibly null node*)
Definition EVP_MD_CTX_node sh (vals:val*(val*(val*val))) (p:val):mpred :=
 (!!(p = nullval) && emp) || EVP_MD_CTX_NNnode sh vals p.

Lemma EVP_MD_CTX_node_null sh vals: EVP_MD_CTX_node sh vals nullval |-- emp.
Proof. apply orp_left; [| rewrite EVP_MD_CTX_NNnode_isptr']; normalize. Qed.

Hint Resolve EVP_MD_CTX_node_null: cancel.

(*According to digest.h, EVP_MD_CTX_md may be invoked even if no digest has not been set, 
  returning null in this case. The other 3 functions are specified to crash in such a 
  situation - we hence strengthen the precondition to rule out these situations*)
Definition EVP_MD_CTX_md_SPEC := DECLARE _EVP_MD_CTX_md
  WITH ctx:val, sh:share, d:val, x:val * (val * val)
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (readable_share sh)
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_node sh (d, x) ctx)
  POST [ tptr (Tstruct _env_md_st noattr) ]
       PROP ()
       LOCAL (temp ret_temp (if Val.eq ctx nullval then nullval else d))
       SEP (EVP_MD_CTX_node sh (d, x) ctx).

Definition EVP_MD_CTX_size_SPEC := DECLARE _EVP_MD_CTX_size
  WITH ctx:val, sh:share, r:EVP_MD_record, d:val, x:val * (val * val)
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (readable_share sh)
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_NNnode sh (d, x) ctx;  EVP_MD_rep r d)
  POST [ tptr (Tstruct _env_md_st noattr) ]
       PROP (readable_share sh)
       LOCAL (temp ret_temp (Vint (Int.repr (EVP_MD_rec_md_size r))))
       SEP (EVP_MD_CTX_NNnode sh (d, x) ctx;  EVP_MD_rep r d).

Definition EVP_MD_CTX_block_size_SPEC := DECLARE _EVP_MD_CTX_block_size
  WITH ctx:val, sh:share, r:EVP_MD_record, d:val, x:val * (val * val)
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (readable_share sh)
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_NNnode sh (d, x) ctx;  EVP_MD_rep r d)
  POST [ tptr (Tstruct _env_md_st noattr) ]
       PROP (readable_share sh)
       LOCAL (temp ret_temp (Vint (Int.repr (EVP_MD_rec_block_size r))))
       SEP (EVP_MD_CTX_NNnode sh (d, x) ctx;  EVP_MD_rep r d).

Definition EVP_MD_CTX_type_SPEC := DECLARE _EVP_MD_CTX_type
  WITH ctx:val, sh:share, r:EVP_MD_record, d:val, x:val * (val * val)
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (readable_share sh)
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_NNnode sh (d, x) ctx;  EVP_MD_rep r d)
  POST [ tptr (Tstruct _env_md_st noattr) ]
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr (NID_of_DigestNID (EVP_MD_rec_type r)))))
       SEP (EVP_MD_CTX_NNnode sh (d, x) ctx;  EVP_MD_rep r d).

Definition Gprog_DigAccessOps : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [EVP_MD_block_size_SPEC; EVP_MD_type_SPEC; EVP_MD_size_SPEC  (*called*);
   EVP_MD_CTX_md_SPEC; EVP_MD_CTX_size_SPEC; EVP_MD_CTX_block_size_SPEC; EVP_MD_CTX_type_SPEC].

Lemma body_EVP_MD_CTX_block_size: semax_body Vprog Gprog_DigAccessOps f_EVP_MD_CTX_block_size EVP_MD_CTX_block_size_SPEC.
Proof.
  start_function. 
  rewrite  EVP_MD_CTX_NNnode_isptr'; Intros.  
  forward_call (ctx, sh, d, x).
    apply sepcon_derives; [apply orp_right2; trivial | cancel].   
  rewrite if_false by (destruct ctx; try contradiction; discriminate). 
  forward_call (d,r).
  forward.
  destruct x as [? [? ?]]. cancel.
  apply orp_left; [ Intros; subst; contradiction | trivial ].
Qed.

Lemma body_EVP_MD_CTX_type: semax_body Vprog Gprog_DigAccessOps f_EVP_MD_CTX_type EVP_MD_CTX_type_SPEC.
Proof.
  start_function. 
  rewrite  EVP_MD_CTX_NNnode_isptr'; Intros.
  forward_call (ctx, sh, d, x).
    apply sepcon_derives; [apply orp_right2; trivial | cancel]. 
  rewrite if_false by (destruct ctx; try contradiction; discriminate).
  forward_call (d, r).
  forward.
  destruct x as [? [? ?]]. cancel.
  apply orp_left; [ Intros; subst; contradiction | trivial ].
Qed.

Lemma body_EVP_MD_CTX_size: semax_body Vprog Gprog_DigAccessOps f_EVP_MD_CTX_size EVP_MD_CTX_size_SPEC.
Proof.
  start_function. 
  rewrite  EVP_MD_CTX_NNnode_isptr'; Intros.
  forward_call (ctx, sh, d, x).
    apply sepcon_derives; [apply orp_right2; trivial | cancel]. 
  rewrite if_false by (destruct ctx; try contradiction; discriminate).
  forward_call (d, r).
  forward.
  destruct x as [? [? ?]]. cancel.
  apply orp_left; [ Intros; subst; contradiction | trivial ].
Qed.

Lemma body_EVP_MD_CTX_md: semax_body Vprog Gprog_DigAccessOps f_EVP_MD_CTX_md EVP_MD_CTX_md_SPEC.
Proof.
  start_function. destruct x as [mddata [pctx pctxops]].
  forward_if (
      PROP ()
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_NNnode sh (d, (mddata, (pctx, pctxops))) ctx)). 
+ clear H. apply orp_left; [ entailer! | unfold EVP_MD_CTX_NNnode; normalize; entailer!].
+ subst. forward.
+ forward. entailer. apply orp_left; normalize.
+ unfold EVP_MD_CTX_NNnode. Intros. 
  forward. forward.
  rewrite data_at_isptr; normalize. 
  rewrite if_false. 2: destruct ctx; try contradiction; discriminate.
  normalize. apply orp_right2. unfold EVP_MD_CTX_NNnode. entailer!.
Qed.  

(*nonnull node*)
Definition EVP_MD_NNnode (sh:share) (vals:reptype (Tstruct _env_md_st noattr)) (p:val):mpred :=
  !!(readable_share sh) &&
  data_at sh (Tstruct _env_md_st noattr) vals p.

Lemma EVP_MD_NNnode_isptr sh vals p:
  EVP_MD_NNnode sh vals p |-- !!(isptr p).
Proof.
  unfold EVP_MD_NNnode. destruct vals. normalize.
  rewrite data_at_isptr. entailer!.
Qed.
Lemma EVP_MD_NNnode_isptr' sh vals p:
  EVP_MD_NNnode sh vals p  = (!!(isptr p) &&  EVP_MD_NNnode sh vals p).
Proof.
  apply pred_ext; [ entailer; apply EVP_MD_NNnode_isptr | entailer!].
Qed.

Lemma EVP_MD_NNnode_validptr sh vals p:  EVP_MD_NNnode sh vals p |-- valid_pointer p.
Proof. unfold EVP_MD_NNnode. entailer!. Qed.

(*a possibly null node*)
Definition EVP_MD_node (vals:reptype (Tstruct _env_md_st noattr))(p:val):mpred :=
 (!!(p = nullval) && emp) || (EX sh:_, EVP_MD_NNnode sh vals p).


Lemma EVP_MD_node_null vals: EVP_MD_node vals nullval |-- emp.
Proof. apply orp_left; [| Intros sh; rewrite EVP_MD_NNnode_isptr' ]; normalize. Qed.

Hint Resolve EVP_MD_node_null: cancel.

Lemma EVP_MD_node_validptr vals p:  EVP_MD_node vals p |-- valid_pointer p.
Proof. unfold EVP_MD_node.
  apply orp_left; normalize. apply valid_pointer_null.
  apply EVP_MD_NNnode_validptr. 
Qed.

Definition get_ctxsize (vals:reptype (Tstruct _env_md_st noattr)):=
  match vals with
    (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) => ctxsize
  end.
Definition get_iniptr (vals:reptype (Tstruct _env_md_st noattr)):=
  match vals with
    (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) => ini
  end.
Definition get_updptr (vals:reptype (Tstruct _env_md_st noattr)):=
  match vals with
    (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) => upd
  end.
Definition get_finptr (vals:reptype (Tstruct _env_md_st noattr)):=
  match vals with
    (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) => fin
  end.

Lemma Valeq_Vint {A} i j (a b:A):
      (if Val.eq (Vint i) (Vint j) then a else b) =
      (if Int.eq i j then a else b).
Proof. 
 remember (Int.eq i j). destruct b0.
+ rewrite ( binop_lemmas2.int_eq_true _ _ Heqb0). rewrite if_true; trivial.
+ remember (Val.eq (Vint i )(Vint j)) as d.
  destruct d; trivial.
  inversion e; subst; simpl in *.
  specialize (int_eq_false_e j j); intuition.
Qed. 

Definition Gprog_cleanup : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [OPENSSL_cleanse_SPEC; OPENSSL_free_SPEC; EVP_MD_CTX_init_SPEC].

(*crashes if ctx==null, so require NNode*)
(*Case 1 (representative case:: ctx->digest==nullref)*)
Definition EVP_MD_CTX_cleanup_SPEC1 := DECLARE _EVP_MD_CTX_cleanup
  WITH ctx:val, sh:share, d:val, mdd:val, pv1:val, pv2:val, 
       vals:reptype (Tstruct _env_md_st noattr)
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (writable_share sh; d=nullval; pv2=nullval)
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_NNnode sh (d, (mdd, (pv1, pv2))) ctx)
  POST [ tint ]
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.one)))
       SEP (data_at_ sh (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr))) ctx).

(*Case 2: md and mdd point to reasonable data*)
Definition EVP_MD_CTX_cleanup_SPEC2 := DECLARE _EVP_MD_CTX_cleanup
  WITH ctx:val, sh:share, d:val, mdd:val, pv1:val, pv2:val, ctxsz: int,
       vals:reptype (Tstruct _env_md_st noattr), dsh:share
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (writable_share sh; pv2=nullval;
            get_ctxsize vals = Vint ctxsz; Int.eq ctxsz Int.zero=false)
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_NNnode sh (d, (mdd, (pv1, pv2))) ctx; EVP_MD_NNnode dsh vals d; 
           memory_block Tsh (Int.unsigned ctxsz) mdd)
  POST [ tint ]
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.one)))
       SEP (data_at_ sh (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr))) ctx; 
            EVP_MD_NNnode dsh vals d).

Lemma body_EVP_MD_CTX_cleanup1: semax_body Vprog Gprog_cleanup f_EVP_MD_CTX_cleanup EVP_MD_CTX_cleanup_SPEC1.
Proof. 
  start_function. unfold EVP_MD_CTX_NNnode. subst. 
  Intros. 
  forward. 
  forward_if (
   PROP ( )
   LOCAL (temp _t'1 (Vint Int.zero); temp _t'12 nullval; temp _ctx ctx)
   SEP (data_at sh (Tstruct _env_md_ctx_st noattr)
          (nullval, (mdd, (pv1, nullval))) ctx)).
{ simpl in H; contradiction. }
{ clear H. forward. entailer!. }
  forward_if (
   PROP ( )
   LOCAL (temp _t'2 (Vint Int.zero); temp _t'1 (Vint Int.zero); temp _t'12 nullval; 
   temp _ctx ctx)
   SEP (data_at sh (Tstruct _env_md_ctx_st noattr)
          (nullval, (mdd, (pv1,nullval))) ctx)).
{ elim H; trivial. }
{ clear H. forward. entailer!. }
  forward_if (
  PROP ( )
  LOCAL (temp _t'2 (Vint Int.zero); temp _t'1 (Vint Int.zero);
         temp _t'12 nullval; temp _ctx ctx)
  SEP (data_at sh (Tstruct _env_md_ctx_st noattr)
       (nullval, (mdd, (pv1,nullval))) ctx)).
{ elim H; trivial. }
{ clear H. forward. entailer!. }
  forward.
  forward_if (
  (PROP ( )
   LOCAL (temp _ctx ctx)
   SEP (data_at sh (Tstruct _env_md_ctx_st noattr)
          (nullval, (mdd, (pv1, nullval))) ctx))).
{ inv H. }
{ forward. entailer!. }
forward_call (ctx, sh, sizeof (Tstruct _env_md_ctx_st noattr)).
forward. cancel.
Qed.

Lemma body_EVP_MD_CTX_cleanup2: semax_body Vprog Gprog_cleanup f_EVP_MD_CTX_cleanup EVP_MD_CTX_cleanup_SPEC2.
Proof. 
  start_function. unfold EVP_MD_CTX_NNnode. subst. rename H0 into CTXsize. rename H1 into CTXsizeNonzero. 
  rewrite  EVP_MD_NNnode_isptr'. Intros. 
  forward. 
  forward_if (
   PROP ( )
   LOCAL (temp _t'1 (Vint Int.one); 
          temp _t'12 d; temp _ctx ctx)
   SEP (data_at sh (Tstruct _env_md_ctx_st noattr)
          (d, (mdd, (pv1, nullval))) ctx; EVP_MD_NNnode dsh vals d;
        memory_block Tsh (Int.unsigned ctxsz) mdd)).
{ clear H. 
  apply denote_tc_test_eq_split; try apply valid_pointer_null.
  apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
    apply EVP_MD_NNnode_validptr. }
{ clear H. forward. 
  unfold EVP_MD_NNnode; Intros. rename H into Rsh1.
  destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *. subst.
  forward. forward. entailer!. simpl. rewrite CTXsizeNonzero; trivial. 
  unfold EVP_MD_NNnode. entailer!. }
{ subst; contradiction. }
  forward_if 
  (PROP ( )
   LOCAL (temp _t'2 (if Val.eq mdd nullval then Vint Int.zero else Vint Int.one); temp _t'1 (Vint Int.one); temp _t'12 d; 
   temp _ctx ctx)
   SEP (data_at sh (Tstruct _env_md_ctx_st noattr)
          (d, (mdd, (pv1, nullval))) ctx; EVP_MD_NNnode dsh vals d;
        memory_block Tsh (Int.unsigned ctxsz) mdd)).
{ clear H. forward.
  forward. 
  + entailer.
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer2. apply memory_block_valid_ptr. intuition.
    specialize (Int.unsigned_range ctxsz); intros.
    destruct (zeq 0 (Int.unsigned ctxsz)). 2: omega.
    apply int_eq_false_e in CTXsizeNonzero. elim CTXsizeNonzero. unfold Int.zero. 
    rewrite e, Int.repr_unsigned; trivial.
  + entailer. destruct mdd; try contradiction. rewrite if_false; [ entailer! | discriminate]. }
{ inv H. }
rewrite memory_block_isptr. Intros. rewrite if_false. 2: destruct mdd; try contradiction; discriminate.
forward_if 
  (PROP ( )
   LOCAL (temp _ctx ctx)
   SEP (data_at sh (Tstruct _env_md_ctx_st noattr) (d, (mdd, (pv1, nullval))) ctx; EVP_MD_NNnode dsh vals d)).
+ clear H. forward. forward.
  unfold EVP_MD_NNnode; Intros. rename H into Rsh1.
  destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]].
  simpl in type, mds, flags, ini, upd, fin, blsize, ctxsize, CTXsize; subst.
  forward.
  forward_call (mdd,  Tsh, Int.unsigned ctxsz).
  { simpl. rewrite Int.repr_unsigned. entailer!. }
  { split. apply writable_share_top. apply Int.unsigned_range_2. }
  forward.
  forward_call (mdd, Int.unsigned ctxsz).
  rewrite sepcon_assoc. apply sepcon_derives. 
  { apply orp_right2. eapply derives_trans. apply data_at_memory_block.
    simpl. rewrite Z.mul_1_l, Z.max_r; trivial.
    apply Int.unsigned_range. }
  { cancel. }
  unfold EVP_MD_NNnode; entailer!.
+ inv H.
+ forward.
  forward_if (PROP ( )
   LOCAL (temp _t'3 nullval; temp _ctx ctx)
   SEP (data_at sh (Tstruct _env_md_ctx_st noattr)
          (d, (mdd, (pv1, nullval))) ctx;
   EVP_MD_NNnode dsh vals d)).
  { contradiction. }
  { clear H. forward. entailer!. }
  forward_call (ctx, sh, sizeof (Tstruct _env_md_ctx_st noattr)).
  forward. cancel.
Time Qed. (*Slow; >  40s*)

(*Case 3:unify*)
Definition EVP_MD_CTX_cleanup_SPEC3 := DECLARE _EVP_MD_CTX_cleanup
  WITH ctx:val, sh:share, d:val, mdd:val, pv1:val, ctxsz: int,
       vals:reptype (Tstruct _env_md_st noattr), dsh:share
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (writable_share sh; 
            get_ctxsize vals = Vint ctxsz; Int.eq ctxsz Int.zero=false)
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_NNnode sh (d, (mdd, (pv1, nullval))) ctx; 
          (!!(d=nullval)&&emp) || 
          (!!(isptr d) && (EVP_MD_NNnode dsh vals d * 
                            ((!!(mdd = nullval)&& emp) || memory_block Tsh (Int.unsigned ctxsz) mdd))))
  POST [ tint ]
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.one)))
       SEP (data_at_ sh (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr))) ctx; 
            EVP_MD_node vals d).

Lemma body_EVP_MD_CTX_cleanup3: semax_body Vprog Gprog_cleanup f_EVP_MD_CTX_cleanup EVP_MD_CTX_cleanup_SPEC3.
Proof. 
  start_function. unfold EVP_MD_CTX_NNnode. subst. rename H into CTXsize. rename H0 into CTXsizeNonzero. 
  Intros.
  focus_SEP 1.
  apply semax_orp_SEPx; Intros; subst.
{ (*d=nullval*)
  forward. 
  forward_if
  (PROP ( )
   LOCAL (temp _t'1 nullval; temp _ctx ctx)
   SEP (data_at sh (Tstruct _env_md_ctx_st noattr)
     (nullval, (mdd, (pv1, nullval))) ctx)).
  { contradiction. }
  { forward. entailer!. }
  forward_if 
  (PROP ( )
   LOCAL (temp _t'2 nullval; temp _ctx ctx)
   SEP (data_at sh (Tstruct _env_md_ctx_st noattr)
          (nullval, (mdd, (pv1, nullval))) ctx)).
   { elim H; trivial. }
   { forward. entailer!. }
   forward_if 
  (PROP ( )
   LOCAL (temp _ctx ctx)
   SEP (data_at sh (Tstruct _env_md_ctx_st noattr)
          (nullval, (mdd, (pv1, nullval))) ctx)).
   { elim H; trivial. }
   { forward. entailer!. }
   forward.
   forward_if 
  (PROP ( )
   LOCAL (temp _ctx ctx)
   SEP (data_at sh (Tstruct _env_md_ctx_st noattr)
          (nullval, (mdd, (pv1, nullval))) ctx)). 
   { contradiction. }
   { forward. entailer!. }
   forward_call (ctx, sh, sizeof (Tstruct _env_md_ctx_st noattr)).
   forward.
   cancel. unfold EVP_MD_NNnode. apply orp_right1. entailer!. }
clear PNd. focus_SEP 1. forward.
forward_if
  (PROP ( )
   LOCAL (temp _t'1 (Vint Int.one); temp _ctx ctx)
   SEP (!! (mdd = nullval) && emp
        || memory_block Tsh (Int.unsigned ctxsz) mdd;
   EVP_MD_NNnode dsh vals d;
   data_at sh (Tstruct _env_md_ctx_st noattr) (d, (mdd, (pv1, nullval)))
     ctx)).
{ clear H.
  apply denote_tc_test_eq_split; try apply valid_pointer_null.
  apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
  apply EVP_MD_NNnode_validptr. }
{ clear H. forward. 
  unfold EVP_MD_NNnode; Intros. rename H into Rsh1.
  destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *. subst.
  forward. forward. entailer!. simpl. rewrite CTXsizeNonzero; trivial.
  unfold EVP_MD_NNnode. entailer!. }
{ subst; contradiction. }
apply semax_orp_SEPx; Intros; subst.
{ (*mdd=nullval*)
  forward_if 
  (PROP ( )
   LOCAL (temp _t'2 nullval; temp _ctx ctx)
   SEP (EVP_MD_NNnode dsh vals d;
   data_at sh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (pv1, nullval)))
     ctx)).
  { forward. forward. entailer!. }
  { inv H. } 
  forward_if (
  (PROP ( )
   LOCAL (temp _ctx ctx)
   SEP (EVP_MD_NNnode dsh vals d;
   data_at sh (Tstruct _env_md_ctx_st noattr)
     (d, (nullval, (pv1, nullval))) ctx))).
  { elim H; trivial. } 
  { forward. entailer!. }
  forward.
  forward_if (PROP ( )
   LOCAL (temp _ctx ctx)
   SEP (EVP_MD_NNnode dsh vals d;
   data_at sh (Tstruct _env_md_ctx_st noattr)
     (d, (nullval, (pv1, nullval))) ctx)).
  { contradiction. }
  { forward. entailer!. }
  forward_call (ctx, sh, sizeof (Tstruct _env_md_ctx_st noattr)).
  forward.
  cancel. apply orp_right2. Exists dsh. trivial . }
rewrite memory_block_isptr. Intros.
forward_if 
  (PROP ( )
   LOCAL (temp _t'2 (Vint Int.one); temp _ctx ctx)
   SEP (memory_block Tsh (Int.unsigned ctxsz) mdd; 
   EVP_MD_NNnode dsh vals d;
   data_at sh (Tstruct _env_md_ctx_st noattr) (d, (mdd, (pv1, nullval)))
     ctx)).
{ forward. forward. entailer!.
  apply denote_tc_test_eq_split; try apply valid_pointer_null.
  apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
  apply memory_block_valid_ptr. intuition. 
    specialize (Int.unsigned_range ctxsz); intros.
    destruct (zeq 0 (Int.unsigned ctxsz)). 2: omega.
    apply int_eq_false_e in CTXsizeNonzero. elim CTXsizeNonzero. unfold Int.zero. 
    rewrite e, Int.repr_unsigned; trivial.
  entailer!. destruct mdd; try contradiction. simpl; trivial. }
{ inv H. }
unfold EVP_MD_NNnode. Intros. rename H into Rsh1. destruct d; try contradiction.
destruct mdd; try contradiction.
forward_if (PROP ( )
   LOCAL (temp _t'2 (Vint Int.one); temp _ctx ctx)
   SEP (
   data_at dsh (Tstruct _env_md_st noattr) vals (Vptr b i);
   data_at sh (Tstruct _env_md_ctx_st noattr)
     (Vptr b i, (Vptr b0 i0, (pv1, nullval))) ctx)).
{ clear H. forward. forward. 
  destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *. subst.
  forward. 
  forward_call (Vptr b0 i0, Tsh, Int.unsigned ctxsz).
  { simpl. rewrite Int.repr_unsigned; entailer!. }
  { split. intuition. apply Int.unsigned_range_2. }
  forward.
  forward_call (Vptr b0 i0, Int.unsigned ctxsz).
  { rewrite distrib_orp_sepcon. apply orp_right2; entailer!.
    rewrite sepcon_assoc. apply sepcon_derives; [ | cancel]. 
    eapply derives_trans. apply data_at_memory_block. simpl.
      rewrite Z.mul_1_l, Z.max_r; trivial.
      apply Int.unsigned_range. }
  entailer!. }
{ inv H. }
forward.
forward_if (PROP ( )
   LOCAL (temp _t'2 (Vint Int.one); 
   temp _ctx ctx)
   SEP (data_at dsh (Tstruct _env_md_st noattr) vals (Vptr b i);
   data_at sh (Tstruct _env_md_ctx_st noattr)
     (Vptr b i, (Vptr b0 i0, (pv1, nullval))) ctx)).
{ contradiction. }
{ forward; entailer!. }
forward_call (ctx, sh, sizeof (Tstruct _env_md_ctx_st noattr)).
forward. cancel. apply orp_right2. Exists dsh. unfold EVP_MD_NNnode; entailer!. 
Qed. 

Definition EVP_MD_CTX_cleanup_SPEC4 := DECLARE _EVP_MD_CTX_cleanup
  WITH ctx:val, sh:share, mdd:val, pv1:val, 
       other: unit + (share * val * reptype (Tstruct _env_md_st noattr))
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
  match other with
   inl _ =>
      PROP (writable_share sh)
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_NNnode sh (nullval, (mdd, (pv1, nullval))) ctx)
  | inr (dsh,d,vals) =>
      PROP (writable_share sh; isptr d)
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_NNnode sh (d, (mdd, (pv1, nullval))) ctx; 
           EX ctxsz:int, !!(get_ctxsize vals = Vint ctxsz /\ Int.eq ctxsz Int.zero=false) &&
           (EVP_MD_NNnode dsh vals d *
           ((!!(mdd = nullval)&& emp) || memory_block Tsh (Int.unsigned ctxsz) mdd)))
  end
  POST [ tint ]
  match other with
   inl _ =>
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.one)))
       SEP (data_at_ sh (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr))) ctx)
  | inr (dsh,d,vals) =>
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.one)))
       SEP (data_at_ sh (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr))) ctx; 
            EVP_MD_NNnode dsh vals d)
  end.
(*could (should?) strengthen at least onde data_at_ to data_at list_repeat .. 0*)

Lemma body_EVP_MD_CTX_cleanup4: semax_body Vprog Gprog_cleanup f_EVP_MD_CTX_cleanup EVP_MD_CTX_cleanup_SPEC4.
Proof. 
  start_function.
destruct other as [ _ | [[dsh d] vals]].
+ (*inl case*)
  unfold EVP_MD_CTX_NNnode; normalize.
  rename H into Wsh.
  forward. 
  forward_if (
   PROP ( )
   LOCAL (temp _t'1 (Vint Int.zero); temp _t'12 nullval; temp _ctx ctx)
   SEP (data_at sh (Tstruct _env_md_ctx_st noattr)
          (nullval, (mdd, (pv1, nullval))) ctx)).
  { simpl in H; contradiction. }
  { clear H. forward. entailer!. }
  forward_if (
   PROP ( )
   LOCAL (temp _t'2 (Vint Int.zero); temp _t'1 (Vint Int.zero); temp _t'12 nullval; 
   temp _ctx ctx)
   SEP (data_at sh (Tstruct _env_md_ctx_st noattr)
          (nullval, (mdd, (pv1,nullval))) ctx)).
  { elim H; trivial. }
  { clear H. forward. entailer!. }
  forward_if (
  PROP ( )
  LOCAL (temp _t'2 (Vint Int.zero); temp _t'1 (Vint Int.zero);
         temp _t'12 nullval; temp _ctx ctx)
  SEP (data_at sh (Tstruct _env_md_ctx_st noattr)
       (nullval, (mdd, (pv1,nullval))) ctx)).
  { elim H; trivial. }
  { clear H. forward. entailer!. }
  forward.
  forward_if (
  (PROP ( )
   LOCAL (temp _ctx ctx)
   SEP (data_at sh (Tstruct _env_md_ctx_st noattr)
          (nullval, (mdd, (pv1, nullval))) ctx))).
  { inv H. }
  { forward. entailer!. }
  forward_call (ctx, sh, sizeof (Tstruct _env_md_ctx_st noattr)).
  forward. cancel.
+ (*inr case*) 
  unfold EVP_MD_CTX_NNnode. Intros ctxsz.
  rename H into Wsh. rename H0 into ctxszH1. rename H1 into ctxszH2.
  clear PNd. focus_SEP 1. forward. 
  forward_if
  (PROP ( )
   LOCAL (temp _t'1 (Vint Int.one); temp _ctx ctx)
   SEP (!! (mdd = nullval) && emp
        || memory_block Tsh (Int.unsigned ctxsz) mdd;
   EVP_MD_NNnode dsh vals d;
   data_at sh (Tstruct _env_md_ctx_st noattr) (d, (mdd, (pv1, nullval)))
     ctx)).
  { clear H.
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
    apply EVP_MD_NNnode_validptr. }
  { clear H. forward. 
    unfold EVP_MD_NNnode; Intros. rename H into Rsh1.
    destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *. subst.
    destruct d; try contradiction.
    forward. forward. entailer!. simpl. rewrite ctxszH2; trivial.
    unfold EVP_MD_NNnode; entailer!. }
  { subst; contradiction. }
  apply semax_orp_SEPx; Intros; subst.
  - (*mdd=nullval*)
    forward_if 
    (PROP ( )
     LOCAL (temp _t'2 nullval; temp _ctx ctx)
     SEP (EVP_MD_NNnode dsh vals d;
     data_at sh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (pv1, nullval))) ctx)).
    { forward. forward. entailer!. }
    { inv H. } 
    forward_if (
      PROP ( )
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_NNnode dsh vals d;
           data_at sh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (pv1, nullval))) ctx)).
    { elim H; trivial. } 
    { forward. entailer!. }
    forward.
    forward_if (PROP ( )
     LOCAL (temp _ctx ctx)
     SEP (EVP_MD_NNnode dsh vals d;
          data_at sh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (pv1, nullval))) ctx)).
    { contradiction. }
    { forward. entailer!. }
    forward_call (ctx, sh, sizeof (Tstruct _env_md_ctx_st noattr)).
    forward. cancel.
  - rewrite memory_block_isptr. Intros.
    forward_if (PROP ( )
     LOCAL (temp _t'2 (Vint Int.one); temp _ctx ctx)
     SEP (memory_block Tsh (Int.unsigned ctxsz) mdd; 
          EVP_MD_NNnode dsh vals d;
          data_at sh (Tstruct _env_md_ctx_st noattr) (d, (mdd, (pv1, nullval))) ctx)).
    { forward. forward. entailer!.
      apply denote_tc_test_eq_split; try apply valid_pointer_null.
      apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
      apply memory_block_valid_ptr. intuition. 
      specialize (Int.unsigned_range ctxsz); intros.
      destruct (zeq 0 (Int.unsigned ctxsz)). 2: omega.
      apply int_eq_false_e in ctxszH2. elim ctxszH2. unfold Int.zero. 
      rewrite e, Int.repr_unsigned; trivial.
      entailer!. destruct mdd; try contradiction. simpl; trivial. }
    { inv H. }
    unfold EVP_MD_NNnode. Intros. rename H into Rsh1. destruct d; try contradiction.
    destruct mdd; try contradiction.
    forward_if (PROP ( )
     LOCAL (temp _t'2 (Vint Int.one); temp _ctx ctx)
     SEP (data_at dsh (Tstruct _env_md_st noattr) vals (Vptr b i);
          data_at sh (Tstruct _env_md_ctx_st noattr) (Vptr b i, (Vptr b0 i0, (pv1, nullval))) ctx)).
    { clear H. forward. forward. 
      destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *. subst.
      forward. 
      forward_call (Vptr b0 i0, Tsh, Int.unsigned ctxsz).
      { simpl. rewrite Int.repr_unsigned; entailer!. }
      { split. intuition. apply Int.unsigned_range_2. }
      forward.
      forward_call (Vptr b0 i0, Int.unsigned ctxsz).
      { rewrite distrib_orp_sepcon; apply orp_right2; entailer!.
        rewrite sepcon_assoc. apply sepcon_derives; [ | cancel]. 
        eapply derives_trans. apply data_at_memory_block. simpl.
        rewrite Z.mul_1_l, Z.max_r; trivial.
        apply Int.unsigned_range. }
      entailer!. }
    { inv H. }
    forward.
    forward_if (PROP ( )
     LOCAL (temp _t'2 (Vint Int.one); temp _ctx ctx)
     SEP (data_at dsh (Tstruct _env_md_st noattr) vals (Vptr b i);
          data_at sh (Tstruct _env_md_ctx_st noattr) (Vptr b i, (Vptr b0 i0, (pv1, nullval))) ctx)).
    { contradiction. }
    { forward; entailer!. }
    forward_call (ctx, sh, sizeof (Tstruct _env_md_ctx_st noattr)).
    forward. cancel. unfold EVP_MD_NNnode; entailer!. 
Qed. 

(*TODO: maybe adapt to use EVP_MD_CTX_cleanup_SPEC4 instead of ...3*)
Definition EVP_MD_CTX_destroy_SPEC := DECLARE _EVP_MD_CTX_destroy
  WITH ctx:val, dsh:share, d:val, vals:reptype (Tstruct _env_md_st noattr)
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP ()
      LOCAL (temp _ctx ctx)
      SEP ((!!(ctx=nullval) && emp) ||
           (!!(isptr ctx) && EX mdd:val, EX pv1:val, EX ctxsz:int,
              (!!(get_ctxsize vals = Vint ctxsz /\ Int.eq ctxsz Int.zero=false)
               && (EVP_MD_CTX_NNnode Tsh (d, (mdd, (pv1, nullval))) ctx * 
                   ((!!(d=nullval)&&emp) || 
                     (!!(isptr d) && (EVP_MD_NNnode dsh vals d * 
                            ((!!(mdd = nullval)&& emp) || memory_block Tsh (Int.unsigned ctxsz) mdd))))))))
  POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP ((!!(ctx=nullval) && emp) || 
            (!!(isptr ctx) &&  ((!!(d=nullval)&&emp) || (!!(isptr d) && EVP_MD_NNnode dsh vals d)))).

Definition Gprog_destroy : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [OPENSSL_free_SPEC; EVP_MD_CTX_cleanup_SPEC4].

Lemma body_EVP_MD_CTX_destroy: semax_body Vprog Gprog_destroy f_EVP_MD_CTX_destroy EVP_MD_CTX_destroy_SPEC.
Proof. 
  start_function.
  apply semax_orp_SEPx; Intros; subst.
{ (*ctx=nullval*)
  forward_if (PROP ( False )  LOCAL (temp _ctx nullval)  SEP (emp)).
  + forward. apply orp_right1; trivial.
  + inv H.
  + normalize. }
Intros mdd pv1 ctxsz. rename H into GS; rename H0 into Ctxsize.
unfold EVP_MD_CTX_NNnode. Intros.
forward_if (PROP ( )
   LOCAL (temp _ctx ctx)
   SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr)
          (d, (mdd, (pv1, nullval))) ctx;
   !! (d = nullval) && emp
   || !! isptr d &&
      (EVP_MD_NNnode dsh vals d *
       (!! (mdd = nullval) && emp
        || memory_block Tsh (Int.unsigned ctxsz) mdd)))).
{ destruct ctx; try contradiction. inv H. }
{ forward. entailer!. }
focus_SEP 1.
apply semax_orp_SEPx; Intros.
+ (*d=null*)
  subst.
  forward_call (ctx, Tsh, mdd, pv1,
              @inl unit (share * val * reptype (Tstruct _env_md_st noattr)) tt).
  { unfold EVP_MD_CTX_NNnode. entailer!. }
  forward_call (ctx, sizeof (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr)))). 
  { rewrite distrib_orp_sepcon, data_at__memory_block.
    apply orp_right2; entailer!. }
  forward. apply orp_right2. entailer!. apply orp_right1; trivial.
+ (*isptr d*)
  forward_call (ctx, Tsh, mdd, pv1,
              @inr unit (share * val * reptype (Tstruct _env_md_st noattr))
                   (dsh, d, vals)).
  { unfold EVP_MD_CTX_NNnode. Exists ctxsz; entailer!. } 
  forward_call (ctx, sizeof (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr)))).
  { rewrite data_at__memory_block, distrib_orp_sepcon. apply orp_right2; entailer!. }
  forward. apply orp_right2. entailer!. apply orp_right2; entailer!.
Qed.

Parameter ERR: val -> mpred. 
Definition OPENSSL_PUT_ERROR_SPEC := DECLARE _ERR_put_error
  WITH a1:val, a2:val, a3:val, ep:val, a5:val
  PRE [ 1%positive OF tint, 
        2%positive OF tint, 3%positive OF tint, 
        4%positive OF (tptr tschar), 5%positive OF tuint ]
      PROP() 
      LOCAL (temp 1%positive a1; temp 2%positive a2; temp 3%positive a3; 
             temp 4%positive ep; temp 5%positive a5)
      SEP (ERR ep)
  POST [ tvoid ]
    PROP () LOCAL () SEP (ERR ep).

Require Import List.  Import ListNotations.

Lemma ptr_comp_Cne_t p q (P: is_pointer_or_null p) (Q: is_pointer_or_null q): 
      typed_true tint (force_val (sem_cmp_pp Cne p q)) <-> ~(p=q).
Proof.
  destruct p; destruct q; try contradiction; simpl in *; subst;
  unfold typed_true, sem_cmp_pp; simpl; split; intros; trivial; try solve [inv H].
+ elim H; trivial.
+ intros N; inv N. rewrite if_true, Int.eq_true in H; trivial; inv H.
+ destruct (eq_block b b0); subst; trivial.
  destruct (Int.eq_dec i i0); subst; [ elim H; trivial | rewrite Int.eq_false; trivial].
Qed.

Lemma ptr_comp_Cne_t' {T} p q 
      (H: typed_true tint (force_val (sem_cmp_pp Cne p q)))
       (a b:T) (P: is_pointer_or_null p)
               (Q: is_pointer_or_null q):
      (if Val.eq p q then a else b) = b.
Proof. apply ptr_comp_Cne_t in H; trivial.
  rewrite if_false; trivial.
Qed.

Lemma ptr_comp_Cne_f p q (P: is_pointer_or_null p) (Q: is_pointer_or_null q): 
      typed_false tint (force_val (sem_cmp_pp Cne p q)) <-> (p=q).
Proof.
  destruct p; destruct q; try contradiction; simpl in *; subst;
  unfold typed_false, sem_cmp_pp; simpl; split; intros; trivial; try solve [inv H].
+ destruct (eq_block b b0); [subst; simpl in H | inv H].
  destruct (Int.eq_dec i i0); subst; trivial.
  rewrite Int.eq_false in H; trivial; inv H. 
+ inv H. rewrite if_true, Int.eq_true; trivial. 
Qed.

Lemma ptr_comp_Cne_f' {T} p q 
      (H: typed_false tint (force_val (sem_cmp_pp Cne p q)))
       (a b:T) (P: is_pointer_or_null p)
               (Q: is_pointer_or_null q):
      (if Val.eq p q then a else b) = a.
Proof. apply ptr_comp_Cne_f in H; trivial.
  rewrite if_true; trivial.
Qed.

Inductive digestInitEx_cases :=
  DT_eq: forall (sh:share) (md pv2:val), digestInitEx_cases
| D_null: forall (sh:share) (md pv2:val), digestInitEx_cases
| DT_neq: forall (sh:share) (d md pv2:val) (dvals:reptype (Tstruct _env_md_st noattr))
                 (ctxsz : int) (dsh:share), digestInitEx_cases.

Definition digestInitEx_pre (c: digestInitEx_cases) (ctx t:val):mpred  :=
match c with
  DT_eq sh md pv2 => !!(writable_share sh)
                     && EVP_MD_CTX_NNnode sh (t, (md, (nullval, pv2))) ctx
| D_null sh md pv2  => !!(writable_share sh)
                     && EVP_MD_CTX_NNnode sh (nullval, (md, (nullval, pv2))) ctx
| DT_neq sh d md pv2 dvals ctxsz dsh => 
      !!(d<>t /\ writable_share sh /\ get_ctxsize dvals = Vint ctxsz /\ 
         Int.ltu Int.zero ctxsz = true)
      && (EVP_MD_CTX_NNnode sh (d, (md, (nullval, pv2))) ctx *
          EVP_MD_NNnode dsh dvals d *
          (!!(md=nullval)&&emp || memory_block Tsh (Int.unsigned ctxsz) md))
end.

Parameter POST33 POST44 POST55: mpred. 
Definition digestInitEx_post (c: digestInitEx_cases) (ctx t rv:val):mpred  :=
match c with
  DT_eq sh md pv2 => !!(rv = Vint (Int.repr 33)) && POST33
| D_null sh md pv2 => (!!(rv= nullval) && 
             data_at sh (Tstruct _env_md_ctx_st noattr) (t, (nullval, (nullval, pv2))) ctx)
         || (!!(rv= Vint (Int.repr 44)) && POST44)
| DT_neq sh d md pv2 dvals ctxsz dsh => 
     (!!(rv= Vint (Int.repr 0)) 
      && data_at dsh (Tstruct _env_md_st noattr) dvals d * 
         data_at sh (Tstruct _env_md_ctx_st noattr) (t, (nullval, (nullval, pv2))) ctx)
  || (!!(rv= Vint (Int.repr 55)) && POST55)
end.

Definition EVP_DigestInit_ex_SPEC := DECLARE _EVP_DigestInit_ex
  WITH ep: val, ctx:val, t:val, e:val, (*d: val, md:val, pv2:val,
       sh:share,*) tsh:share, c: digestInitEx_cases,
       tvals:reptype (Tstruct _env_md_st noattr)
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr),
        _engine OF tptr (Tstruct _engine_st noattr) ]
      PROP (exists ctxsz', get_ctxsize tvals = Vint ctxsz' /\
               (Int.unsigned ctxsz' <= 0 \/ 4 <= Int.unsigned ctxsz' <= Int.max_unsigned);
            exists ini', get_iniptr tvals = ini' /\ is_pointer_or_null ini')
      LOCAL (gvar ___stringlit_1 ep; temp _type t; temp _ctx ctx; temp _engine e)
      SEP (ERR ep; 
           (*EVP_MD_CTX_NNnode sh (d, (md, (nullval, pv2))) ctx;*)
           EVP_MD_NNnode tsh tvals t; 
           digestInitEx_pre c ctx t)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERR ep; EVP_MD_NNnode tsh tvals t; digestInitEx_post c ctx t rv).

Definition Gprog_DigestInit_ex : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [EVP_DigestInit_ex_SPEC; OPENSSL_PUT_ERROR_SPEC; OPENSSL_free_SPEC; OPENSSL_malloc_SPEC].

Lemma body_DigestInit_ex: semax_body Vprog Gprog_DigestInit_ex f_EVP_DigestInit_ex EVP_DigestInit_ex_SPEC.
Proof. 
  start_function. destruct H as [ctxsz' [CTXSZ1' CTXSZ2']] .
  destruct H0 as [ini'' [ getini' Ini']].
  rewrite EVP_MD_NNnode_isptr'; unfold EVP_MD_NNnode; Intros. rename H into TSH.
  destruct c; normalize.
+ (* Case DT_eq*)
  simpl; Intros; subst. rename H into SH.
  rewrite data_at_isptr with (p:=ctx); Intros.
  forward.
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _type t;
           temp _ctx ctx; temp _engine e)
    SEP (ERR ep;
         data_at sh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, pv2))) ctx;
         data_at tsh (Tstruct _env_md_st noattr) tvals t)).
  - apply ptr_comp_Cne_t in H; congruence.
  - forward. entailer!.
  - forward.
    destruct tvals as [type' [mds' [flags' [ini'' [upd' [fin' [blsize' ctxsize'']]]]]]]. 
    simpl in type', mds', flags', ini'', upd', fin', ctxsize'', blsize', CTXSZ1', CTXSZ2', Ini'; subst.
    simpl. forward. admit. (*Call ini'*) 
+ (* Case D_null*)
  simpl; Intros; subst. rename H into SH.
  rewrite data_at_isptr with (p:=ctx); Intros.
  forward.
  forward_if (
     PROP ( )
     LOCAL (gvar ___stringlit_1 ep;
            temp _type t; temp _ctx ctx; temp _engine e)
     SEP (ERR ep;
          data_at tsh (Tstruct _env_md_st noattr) tvals t;
          ( !!(Int.unsigned ctxsz' <= 0)
             && data_at sh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, pv2))) ctx)
           || (!!(0 < Int.unsigned ctxsz')
               && EX m:_, !!(malloc_compatible (Int.unsigned ctxsz') m) &&
                  data_at sh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, pv2))) ctx *
                  memory_block Tsh (Int.unsigned ctxsz') m))).
  2: solve [apply ptr_comp_Cne_f in H; simpl; trivial; subst; try contradiction; destruct t; try contradiction; trivial]. 
  - clear H.
    forward.
    forward_if (PROP ( )
      LOCAL (temp _t'1 nullval; gvar ___stringlit_1 ep; temp _type t; 
             temp _ctx ctx; temp _engine e)
      SEP (ERR ep;
           data_at sh (Tstruct _env_md_ctx_st noattr) (nullval, (md, (nullval, pv2))) ctx;
           data_at tsh (Tstruct _env_md_st noattr) tvals t));
     [ solve [contradiction] | solve [forward ; entailer!] | ].
    forward_if (
      PROP ( )
      LOCAL (gvar ___stringlit_1 ep;
             temp _type t; temp _ctx ctx; temp _engine e)
      SEP (ERR ep;
           data_at sh (Tstruct _env_md_ctx_st noattr) (nullval, (md, (nullval, pv2))) ctx;
           data_at tsh (Tstruct _env_md_st noattr) tvals t));
     [ elim H; trivial | forward; entailer! | ].
    forward. simpl.
    destruct tvals as [type' [mds' [flags' [ini' [upd' [fin' [blsize' ctxsize'']]]]]]]. 
    simpl in type', mds', flags', ini', upd', fin', ctxsize'', blsize', CTXSZ1', CTXSZ2', Ini'; subst; simpl.
    rewrite eval_cast_neutral_isptr; trivial; simpl.
    forward. 
    forward_if (
      PROP ( )
      LOCAL (gvar ___stringlit_1 ep; temp _type t; 
             temp _ctx ctx; temp _engine e)
      SEP (ERR ep;
           data_at tsh (Tstruct _env_md_st noattr)
              (type', (mds', (flags', (ini', (upd', (fin', (blsize', Vint ctxsz'))))))) t;
           ( !!(Int.unsigned ctxsz' <= 0)
             && data_at sh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, pv2))) ctx)
           || (!!(0 < Int.unsigned ctxsz')
               && EX m:_, !!(malloc_compatible (Int.unsigned ctxsz') m) &&
                  data_at sh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, pv2))) ctx *
                  memory_block Tsh (Int.unsigned ctxsz') m))).
    { destruct CTXSZ2'; [ omega | clear H]. forward.
      forward_call (Int.unsigned ctxsz'). rewrite Int.repr_unsigned; entailer!. 
      Intros m. forward. forward. deadvars.
      apply semax_orp_SEPx; Intros; subst.
      + (*m==null*)
        rewrite eval_cast_neutral_is_pointer_or_null; simpl; trivial.
        forward_if (PROP (False) LOCAL () SEP ()).
        * clear H.
          forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                 ep, Vint (Int.repr 177)). 
          forward. Exists nullval. entailer!.
          unfold EVP_MD_NNnode; entailer!. apply orp_right1. cancel. 
        * inv H.
        * intros. unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
          old_go_lower. clear H. destruct ek; simpl; normalize. 
      + (*m<>null*)
        rename H into M. 
        rewrite memory_block_isptr; Intros.
        rewrite eval_cast_neutral_isptr; simpl; trivial.
        forward_if (
          PROP ( )
          LOCAL (gvar ___stringlit_1 ep; temp _type t; 
                 temp _ctx ctx; temp _engine e)
          SEP (memory_block Tsh (Int.unsigned ctxsz') m; 
               ERR ep;
               data_at sh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, pv2))) ctx;
               data_at tsh (Tstruct _env_md_st noattr)
                 (type', (mds', (flags', (ini', (upd', (fin', (blsize', Vint ctxsz'))))))) t)).
        * clear H.
          apply denote_tc_test_eq_split; [ apply sepcon_valid_pointer1 | apply valid_pointer_null].
          apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
          apply memory_block_valid_ptr. intuition. omega.
        * subst m; contradiction.
        * clear H. forward. entailer!.
        * intros. unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
          old_go_lower. clear H. destruct ek; simpl; normalize. entailer!. 
          apply orp_right2. Exists m; entailer!. } 
    { destruct CTXSZ2'; [ clear H | omega ]. forward. entailer!.
      apply orp_right1; trivial. }
    intros. unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
    old_go_lower. clear H. destruct ek; simpl; normalize. entailer!.
  - focus_SEP 2.
    destruct tvals as [type' [mds' [flags' [ini' [upd' [fin' [blsize' ctxsize'']]]]]]]. 
    simpl in type', mds', flags', ini', upd', fin', ctxsize'', blsize', CTXSZ1', CTXSZ2', Ini'; subst; simpl.
    apply semax_orp_SEPx; Intros.
    * rename H into NONPOS. forward. forward. admit. (*Call ini'*)
    * rename H into POS. Intros m. rename H into M. forward. forward. admit. (*Call ini'*)
+ (*Case DT_neq*)
  simpl; Intros; subst. rename H into DT. rename H0 into SH. 
  rename H1 into CTXSZ1. rename H2 into CTXSZ2.
  rewrite EVP_MD_NNnode_isptr'; unfold EVP_MD_NNnode; Intros. rename H into DSH.
  freeze [4] MD. freeze [4] D.
  (*destruct dvals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
  simpl in type, mds, flags,ini, upd, fin, ctxsize, blsize, CTXSZ1.
  destruct tvals as [type' [mds' [flags' [ini' [upd' [fin' [blsize' ctxsize'']]]]]]]. 
  simpl in type', mds', flags',ini', upd', fin', ctxsize'', blsize', CTXSZ1', CTXSZ2', Ini'; subst; simpl.
  *)
  forward. thaw D. freeze [4] CTX.
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep;
           temp _type t; temp _ctx ctx; temp _engine e)
    SEP ((EX m : val,
          !! (0 < Int.unsigned ctxsz' /\ malloc_compatible (Int.unsigned ctxsz') m)
          && data_at sh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, pv2))) ctx *
             memory_block Tsh (Int.unsigned ctxsz') m)
        || !! (0 >= Int.unsigned ctxsz')
           && data_at sh (Tstruct _env_md_ctx_st noattr) (t, (nullval, (nullval, pv2))) ctx;
         ERR ep; 
         data_at tsh (Tstruct _env_md_st noattr) tvals (*(type', (mds', (flags', (ini', (upd', (fin', (blsize', Vint ctxsz')))))))*) t;
         data_at dsh (Tstruct _env_md_st noattr) dvals (*(type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz)))))))*) d)).
  2: solve [apply ptr_comp_Cne_f in H; trivial; try contradiction; destruct t; try contradiction; trivial].
  { clear H.
    unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
    thaw CTX. 
    freeze [1;4] DTFR. forward.
    forward_if (
      PROP ( )
      LOCAL (temp _t'1 (Vint Int.one); gvar ___stringlit_1 ep; temp _type t; temp _ctx ctx; temp _engine e)
      SEP (FRZL DTFR; FRZL MD; ERR ep;
           data_at sh (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ctx)).
    { clear H. apply denote_tc_test_eq_split; 
          [apply sepcon_valid_pointer1 | apply valid_pointer_null].
      apply sepcon_valid_pointer1; apply sepcon_valid_pointer1.
      thaw DTFR. apply sepcon_valid_pointer1. entailer!. }
    { clear H. forward. unfold POSTCONDITION, abbreviate; clear POSTCONDITION; thaw DTFR.
      freeze [1;2;3;4] REST.
      destruct dvals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
      simpl in type, mds, flags,ini, upd, fin, ctxsize, blsize, CTXSZ1. subst; simpl.
      forward. forward. entailer!. simpl. unfold Int.zero in CTXSZ2; rewrite CTXSZ2; trivial.
      thaw REST. cancel. }
    { subst d; contradiction. }
    forward_if (
      PROP ( )
      LOCAL (gvar ___stringlit_1 ep; 
             temp _type t; temp _ctx ctx; temp _engine e)
      SEP (FRZL DTFR; ERR ep;
           data_at sh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, pv2))) ctx)).
    { clear H. forward. unfold POSTCONDITION, abbreviate; clear POSTCONDITION; thaw DTFR. thaw MD.
      freeze [0;1;3] REST.
      (*free*) forward_call (md, Int.unsigned ctxsz).
      forward. entailer!. thaw REST. cancel. }
    { inv H. }
    forward. simpl. rewrite sem_cast_neutral_ptr; simpl; trivial.
    thaw DTFR. freeze [0; 2;3] FR3.
    destruct tvals as [type' [mds' [flags' [ini' [upd' [fin' [blsize' ctxsize'']]]]]]]. 
    simpl in type', mds', flags',ini', upd', fin', ctxsize'', blsize', CTXSZ1', CTXSZ2', Ini'; subst; simpl.
    forward. thaw FR3. freeze [0] FR_D.
    forward_if (
     PROP ( )
     LOCAL (gvar ___stringlit_1 ep;
            temp _type t; temp _ctx ctx; temp _engine e)
     SEP (FRZL FR_D; ERR ep;data_at tsh (Tstruct _env_md_st noattr)
     (type',
     (mds',
     (flags', (ini', (upd', (fin', (blsize', Vint ctxsz'))))))) t;
          (!!(0 < Int.unsigned ctxsz') 
           && (EX m:val, !!(malloc_compatible (Int.unsigned ctxsz') m) &&
                 data_at sh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, pv2))) ctx *
                 memory_block Tsh (Int.unsigned ctxsz') m))
          || (!!(0 >= Int.unsigned ctxsz') 
              && data_at sh (Tstruct _env_md_ctx_st noattr)
                 (t, (nullval, (nullval, pv2))) ctx))).
     + (*0 < Int.unsigned ctxsz'*)
       rename H into CTXSZ'. 
       forward. 
       forward_call (Int.unsigned ctxsz').
       { rewrite Int.repr_unsigned; entailer!. }
       { destruct CTXSZ2'; omega. } 
       Intros m. freeze [4] FR_T.
       forward. forward. deadvars. simpl.
       focus_SEP 1. apply semax_orp_SEPx; Intros; subst.
       { (*m==null*)
         forward_if (PROP (False) LOCAL () SEP ()).
         *  clear H.
            forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                ep, Vint (Int.repr 177)). 
            forward. Exists nullval. entailer!. 
            unfold EVP_MD_NNnode. entailer!. thaw FR_T. cancel.
            apply orp_right1. thaw FR_D. cancel. 
       * inv H. 
       * intros. unfold overridePost. old_go_lower. clear H.
             destruct (EqDec_exitkind ek EK_normal). entailer!. cancel. }
       { (*m <> null*)
         rename H into M. rewrite memory_block_isptr; Intros.
         freeze [1;2;3;4] FR3. 
         forward_if (PROP ( )
            LOCAL (temp _t'7 m; gvar ___stringlit_1 ep; temp _type t; temp _ctx ctx; temp _engine e) 
            SEP (FRZL FR3; memory_block Tsh (Int.unsigned ctxsz') m)).
         * clear H.
           apply denote_tc_test_eq_split; 
            [apply sepcon_valid_pointer2 | apply valid_pointer_null].
           apply memory_block_valid_ptr. intuition. omega. 
         * destruct m; try contradiction. subst; inv H.
         * forward. entailer!. 
         * intros. unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
           old_go_lower. clear H.
           destruct ek; simpl; normalize. entailer!.
           thaw FR3; thaw FR_T; normalize. cancel. 
           apply orp_right1. Exists (eval_id _t'7 rho). entailer!. } 
     + (*Case 0 >= Int.unsigned ctxsz' *)
       rename H into CTXSZ'.
       forward. entailer!. apply orp_right2. cancel.
     + intros. unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
           old_go_lower. clear H.
           destruct ek; simpl; normalize. entailer!.
           thaw FR_D. cancel. apply orp_left; Intros.
       - Intros m. apply orp_right1. Exists m. entailer!.
       - apply orp_right2. entailer!. } 
  apply semax_orp_SEPx. 
  - Intros m. freeze [1;2;4] FR5. forward.
    destruct tvals as [type' [mds' [flags' [ini' [upd' [fin' [blsize' ctxsize'']]]]]]]. 
    simpl in type', mds', flags',ini', upd', fin', ctxsize'', blsize', CTXSZ1', CTXSZ2', Ini'; subst; simpl.
    forward. admit. (*call ini'*)
  - Intros. freeze [1;3] FR5. forward.
    destruct tvals as [type' [mds' [flags' [ini' [upd' [fin' [blsize' ctxsize'']]]]]]]. 
    simpl in type', mds', flags',ini', upd', fin', ctxsize'', blsize', CTXSZ1', CTXSZ2', Ini'; subst; simpl.
    forward. admit. (*call ini'*)
Admitted.
(*
admit. thaw FR; thaw FR_T; normalize. cancel. 
           apply orp_right1. Exists (eval_id _t'7 rho). entailer!. 
      

         Exists m. destruct (eq_dec ek EK_normal); simpl; entailer!.
         subst; simpl. Intros. entailer!. admit. 
         admit. } }
  { (*Case t=d*)
    apply ptr_comp_Cne_f in H; subst; trivial.
    forward. entailer!. }


     apply orp_right2. Exists (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) ctxsz dsh. 
     simpl. entailer!. } forward_call 

 forward. ; apply EVP_MD_NNnode_validptr.
      rewrite (ptr_comp_Cne_t' _ _ HT); trivial. apply ptr_comp_Cne_t in HT; trivial.
    assert (Auxvals: exists auxvals1: reptype (Tstruct _env_md_ctx_st noattr),
        auxvals1 = (d, (md, (nullval, pv2)))).
    { eexists; reflexivity. }
    destruct Auxvals as [auxvals1 Auxvals1].
    apply semax_seq with (Q:= EX mdd:_,
       PROP ()
       LOCAL (gvar ___stringlit_1 ep; temp _type t; temp _ctx ctx; 
              temp _t'1 mdd; temp _engine e)
       SEP ((!! (d = nullval /\ mdd=nullval) && emp)
            || (EX dvals : reptype (Tstruct _env_md_st noattr),
                (EX ctxsz : int,
                 (EX dsh : share,
                  !! (get_ctxsize dvals = Vint ctxsz /\
                      Int.ltu Int.zero ctxsz = true /\ mdd=Vint Int.one) 
                  && (EVP_MD_NNnode dsh dvals d *
                      (!! (md = nullval) && emp || memory_block Tsh (Int.unsigned ctxsz) md)))));
            ERR ep; EVP_MD_NNnode tsh tvals t;
            data_at sh (Tstruct _env_md_ctx_st noattr) auxvals1 ctx)). 
    { apply semax_orp_SEPx; Intros; subst.
      + (*d==null*)
        clear HT; rewrite EVP_MD_NNnode_isptr'; Intros. 
        forward_if  (PROP ( )
           LOCAL (temp _t'1 nullval; gvar ___stringlit_1 ep;
                  temp _type t; temp _ctx ctx; temp _engine e)
           SEP (ERR ep;
                data_at sh (Tstruct _env_md_ctx_st noattr) (nullval, (md, (nullval, pv2))) ctx;
                EVP_MD_NNnode tsh tvals t)); 
         [ solve [contradiction] | solve [clear H; forward; entailer!] | ].
        - intros. old_go_lower. clear H. unfold overridePost.
          destruct ek; simpl; entailer!. Exists nullval. entailer!. apply orp_right1; entailer!.
      + (*isptr d*)
        Intros dvals ctxsz dsh. rename H into CTXSZ1. rename H0 into CTXSZ2. freeze [1;2;4] FR1.
        rewrite EVP_MD_NNnode_isptr'; Intros. 
        forward_if (PROP ( )
           LOCAL (temp _t'1 (Vint Int.one); gvar ___stringlit_1 ep; 
                  temp _type t; temp _ctx ctx; temp _engine e)
           SEP (EVP_MD_NNnode dsh dvals d; FRZL FR1;
                data_at sh (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ctx));
          [ clear H | clear H | subst; contradiction |].
        - apply denote_tc_test_eq_split; 
          [apply sepcon_valid_pointer1 | apply valid_pointer_null].
          apply sepcon_valid_pointer2; apply EVP_MD_NNnode_validptr.
        - forward. 
          destruct dvals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
          simpl in type, mds, flags,ini, upd, fin, ctxsize, blsize, CTXSZ1.
          unfold EVP_MD_NNnode; Intros. subst. forward. forward.
          entailer!. simpl. unfold Val.of_bool. unfold Int.zero in CTXSZ2; rewrite CTXSZ2; trivial. 
          unfold EVP_MD_NNnode. entailer!. 
        - intros. old_go_lower. clear H. unfold overridePost. 
          destruct ek; simpl; entailer!. Exists (Vint Int.one). (* rewrite if_false. 2: destruct d; try contradiction; discriminate.*)
          thaw FR1. entailer!. apply orp_right2. Exists dvals ctxsz dsh. entailer!. } 
    unfold MORE_COMMANDS, abbreviate. Intros mdd.
    assert (Auxvals: exists auxvals2: reptype (Tstruct _env_md_ctx_st noattr),
        auxvals2 = (d, (if Val.eq d nullval then md else nullval, (nullval, pv2)))).
    { eexists; reflexivity. }
    destruct Auxvals as [auxvals2 Auxvals2].
    forward_if ( PROP ()
      LOCAL (gvar ___stringlit_1 ep; temp _type t; 
             temp _ctx ctx; temp _engine e)
      SEP (!! (d = nullval /\ mdd = nullval) && emp
           || (EX dvals : reptype (Tstruct _env_md_st noattr),
              (EX ctxsz : int,
               (EX dsh : share,
                !! (get_ctxsize dvals = Vint ctxsz /\
                    Int.ltu Int.zero ctxsz = true) &&
                (EVP_MD_NNnode dsh dvals d))));
           ERR ep; EVP_MD_NNnode tsh tvals t;
           data_at sh (Tstruct _env_md_ctx_st noattr) auxvals2 ctx)).
   { apply semax_orp_SEPx; Intros; subst; [ inv H |].
     Intros dvals ctxsz dsh. rewrite EVP_MD_NNnode_isptr'; Intros. 
     destruct dvals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
     simpl in type, mds, flags,ini, upd, fin, ctxsize, blsize, H0. subst; simpl.
     freeze [0;2;3] FR1. forward.
     (*free*)forward_call (md, Int.unsigned ctxsz).
     forward. rewrite if_false by (destruct d; try contradiction; discriminate). 
     entailer!. thaw FR1. cancel.
     apply orp_right2. Exists (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) ctxsz dsh. 
     simpl. entailer!. }
   { apply semax_orp_SEPx; Intros; subst.
     + clear H. forward. entailer!. apply orp_right1. entailer!.
     + Intros dvals ctxsz dsh. subst; inv H. }
   
   (*Line 173 ctx->digest = type;*)
   subst auxvals2 auxvals1. forward.
   freeze [0;1;3] FR1.
   destruct tvals as [type' [mds' [flags' [ini' [upd' [fin' [blsize' ctxsize'']]]]]]]. 
   simpl in type', mds', flags',ini', upd', fin', ctxsize'', blsize', CTXSZ'; subst.
   unfold EVP_MD_NNnode; Intros. rename H into TSH.
   forward. thaw FR1. rewrite data_at_isptr with (p:=t). Intros.
   simpl. freeze [0] FR2. freeze [0;3] FR3. 
   forward_if (
     PROP ( )
     LOCAL (temp _t'6 (Vint ctxsz'); gvar ___stringlit_1 ep;
            temp _type t; temp _ctx ctx; temp _engine e)
     SEP (FRZL FR3; ERR ep;
          (!!(0 < Int.unsigned ctxsz') 
           && (EX m:val, !!(malloc_compatible (Int.unsigned ctxsz') m) &&
                 data_at sh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, pv2))) ctx *
                 data_at_ Tsh (tarray tuchar (Int.unsigned ctxsz')) m))
          || (!!(0 >= Int.unsigned ctxsz') 
              && data_at sh (Tstruct _env_md_ctx_st noattr)
                 (t, (if Val.eq d nullval then md else nullval, (nullval, pv2))) ctx))).
   + (*0 < Int.unsigned ctxsz'*)
     rename H into CTXSZ'. unfold POSTCONDITION; clear POSTCONDITION. thaw FR3.
     forward. 
     forward_call (Int.unsigned ctxsz'). rewrite Int.repr_unsigned; entailer!. 
     admit. (*4 <= Int.unsigned ctxsz' <= Int.max_unsigned*) 
     Intros m. forward. forward. deadvars.
     apply semax_orp_SEPx; Intros; subst.
     { (*m==null*)
       forward_if (PROP (False) LOCAL () SEP ()).
       *  clear H.
          forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                ep, Vint (Int.repr 177)). 
          forward. Exists nullval. entailer!. thaw FR2.
          rewrite <- exp_sepcon2. cancel. 
          rewrite <- exp_sepcon1. unfold EVP_MD_NNnode. entailer!.
          admit. (*POSTCOND*)
       * inv H.
       * intros. unfold overridePost. old_go_lower. clear H.
             destruct (EqDec_exitkind ek EK_normal). entailer!. trivial. }
     { (*m <> null*)
       rename H into M. rewrite memory_block_isptr; Intros.
       freeze [1;2;3;4] FR3. 
       forward_if (PROP ( )
          LOCAL (temp _t'7 (force_val (sem_cast (tptr tvoid) (tptr tvoid) m));
             temp _t'6 (Vint ctxsz'); 
             gvar ___stringlit_1 ep; temp _type t; temp _ctx ctx; temp _engine e) 
          SEP (FRZL FR3; memory_block Tsh (Int.unsigned ctxsz') m)).
       * clear H.
         apply denote_tc_test_eq_split; 
          [apply sepcon_valid_pointer2 | apply valid_pointer_null].
         apply memory_block_valid_ptr. intuition. admit. (*Int.unsigned ctxsz' > 0*)
       * destruct m; try contradiction. subst; inv H.
       * forward. entailer!. 
       * intros. old_go_lower. clear H.
         unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
         destruct (eq_dec ek EK_normal).
         subst; simpl. Intros. entailer!. admit. 
         admit. } }
  { (*Case t=d*)
    apply ptr_comp_Cne_f in H; subst; trivial.
    forward. entailer!. }

  forward. thaw FR1.
  destruct (Val.eq d t).
  + subst.
    destruct tvals as [type' [mds' [flags' [ini' [upd' [fin' [blsize' ctxsize'']]]]]]]. 
    simpl in type', mds', flags',ini', upd', fin', ctxsize'', blsize', CTXSZ'; subst.
    unfold EVP_MD_NNnode; Intros. rename H into TSH.
    forward. entailer!. admit. (* is_pointer_or_null ini'*) 
    admit. (*invocation of ini'*) 
  + focus_SEP 2.
    apply semax_orp_SEPx; Intros.
    - (*d=null*)
      subst. admit. (*FAILS!*)
    - Intros dvals ctxsz dsh.
      destruct dvals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
    simpl in type, mds, flags, ini, upd, fin, ctxsize, blsize, H; subst.
    unfold EVP_MD_NNnode; Intros. forward. entailer!. admit. (* is_pointer_or_null ini*) 
    admit. (*invocation of ini*)  rename H into TSH.
    forward. entailer!. admit. (* is_pointer_or_null ini'*)  forward.
     - forward. omega. } entailer!.
          apply sepcon_valid_pointer2; apply EVP_MD_NNnode_validptr.  deadvars!. normalize. cancel. ! sepcon_assoc. rewrite sepcon_comm. rewrite <- ! sepcon_assoc.
          normalize. apply orp_left; Intros. cancel. 
          Exists (default_val (Tstruct _env_md_st noattr)). 
          ; entailer!.
             apply orp_right1. entailer!. 
           * inv H. 
           * intros. unfold overridePost. old_go_lower. clear H.
             destruct (EqDec_exitkind ek EK_normal). entailer!. trivial.
         - normalize. assert_PROP (isptr m) as Hm by entailer!. thaw FR3.
   + (*0 >= Int.unsigned ctxsz'*)
     rename H into CTXSZ'.
     forward. entailer!. apply orp_right2. cancel. Exists  remember (Int.lt Int.zero ctxsz') as q.
     destruct q. rewrite if_false at 2.
   forward_if ( EX m: val,
     PROP ( )
     LOCAL (temp _t'6 (Vint ctxsz'); gvar ___stringlit_1 ep;
            temp _type t; temp _ctx ctx; temp _engine e)
     SEP (FRZL FR2; ERR ep;
          data_at sh (Tstruct _env_md_ctx_st noattr) 
            (t, m, (nullval, pv2))) ctx).


          data_at tsh (Tstruct _env_md_st noattr)
            (type', (mds', (flags', (ini', (upd', (fin', (blsize', Vint ctxsz'))))))) t)).

   { entailer!. subst; simpl.
     freeze [0;2;3] FR1. forward. forward. Focus 2. 2: inv H. |]. dvals  normalize.
        - thaw FR2. cancel. Intros dvals, ctx unfold typed_true in H.  simpl in H.
      
   freeze [0;2;3] FR2.
        forward_if (PROP ( )
          LOCAL (gvar ___stringlit_1 ep;  temp _type t; temp _ctx ctx; temp _engine e)
          SEP (FRZL FR2;
               data_at sh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, pv2))) ctx));
        [ clear H | solve [inv H] | ].
        - forward. 
          (*free*)forward_call (md, Int.unsigned ctxsz).
          forward. entailer!.
        - thaw FR2. cancel.
remember (Int.ltu (Int.repr 0) ctxsize).
        destruct b.x eadmit. 
      + }
    - apply sepcon_valid_pointer1. 

    assert (exists XX: environ -> mpred, XX =
     (EX t1v:val,
      PROP ( )
      LOCAL (gvar ___stringlit_1 ep;  
             temp _t'1 t1v;
             temp _type t; temp _ctx ctx; temp _engine e)
      SEP (ERR ep;
           data_at sh (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ctx; 
           EVP_MD_NNnode tsh tvals t;
           if Val.eq d nullval then !!(t1v=nullval)&&emp 
           else EX dsh:share, EX ctxsz : int,
                !!(get_ctxsize dvals = Vint ctxsz /\
                   Int.eq ctxsz Int.zero = false /\ t1v=Vint ctxsz)
                && EVP_MD_NNnode dsh dvals d))).  environ -> mpred as XX.
    { clear H. 
      apply denote_tc_test_eq_split; [ apply sepcon_valid_pointer2; apply EVP_MD_node_validptr | apply valid_pointer_null]. }
    { forward. focus_SEP 3.
      apply semax_orp_SEPx; Intros; [ subst; contradiction | unfold EVP_MD_NNnode; Intros dsh].
      rename H into Pd. rename H0 into TSH. rename H1 into DSH.
      destruct dvals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
      simpl in type, mds, flags,ini, upd, fin, ctxsize, blsize, HD.
      destruct (HD Pd) as [ctxsz [? ?]]; clear HD; subst.      
      forward. forward. rewrite if_false by (destruct d; try contradiction; discriminate).
      go_lower. Exists dsh ctxsz. unfold EVP_MD_NNnode. normalize.
      apply andp_right; [ apply prop_right; repeat split; trivial | cancel ]. }
    { forward. subst. rewrite if_true; trivial. entailer!. cancel. }
    
x
 cancel.
      apply orp_left; entailer!. unfold 
       entailer!.
        apply sepcon_valid_pointer2. apply EVP_MD_NNnode_validptr.
      apply sepcon_valid_pointer2. normalize. 
    - apply sepcon_valid_pointer1. 
  { apply ptr_comp_Cne_f in H; trivial; subst d. 
    forward. entailer!. }

  (*call init*)
  forward. forward.
    Intros dvals. admit. }
  {  
    apply semax_orp_SEPx; Intros; subst.
    + admit.
    + Intros dsh. rewrite if_true.
   ). 
  focus_SEP 2.
(*Case t==nullval*)
apply 
*)

Definition mdDATA sh sz data md: mpred :=
  (!!(md=nullval) && emp) || ((!!isptr md) && data_at sh (tarray tuchar (Int.unsigned sz)) data md).

Lemma mdDATA_validptr ctxsz sh data md (SH: readable_share sh)
      (SZ: sizeof (tarray tuchar (Int.unsigned ctxsz)) > 0):
      mdDATA sh ctxsz data md |-- valid_pointer md.
Proof. apply orp_left; normalize. apply valid_pointer_null. apply data_at_valid_ptr.
  intuition. trivial.
Qed. 


Inductive copyEx_cases :=
  ictxNull: copyEx_cases
| inDigestNull: forall (ish:share) (md pv1 pv2 :val), copyEx_cases
| inDataNull: forall (ish:share) (d pv1 pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (d' md' pv1': val), copyEx_cases
| equalDigests_outDataNull: forall (ish:share) (d md pv1 pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (pv1': val)
                      (imdsh:share) (idata:list int) (ctxsz: int), copyEx_cases
| equalDigests_outDataPtr: forall (ish:share) (d md pv1 pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (pv1': val)
                      (imdsh:share) (idata:list int) (ctxsz: int)
                      (md':val), copyEx_cases
| outDigest_Null: forall (ish:share) (d md pv1 pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (md' pv1': val)
                      (imdsh:share) (idata:list int) (ctxsz: int), copyEx_cases
| distinctDigests: forall (ish:share) (d md pv1 pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (d' md' pv1': val)
                      (imdsh:share) (idata:list int) (ctxsz: int)
                      (dsh':share) (vals' : reptype (Tstruct _env_md_st noattr))(ctxsz': int), copyEx_cases(*.
| indataPtr: forall (ish:share) (d md pv1 pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (d' md' pv1': val)
                      (idsh:share) (idata:list val), copyEx_cases*).

Definition copyExPre (c:copyEx_cases) (ictx octx:val) : mpred :=
match c with 
  ictxNull => !!(ictx=nullval)&&emp
| inDigestNull ish md pv1 pv2 => !!(isptr ictx /\ readable_share ish)
                            && EVP_MD_CTX_NNnode ish (nullval, (md, (pv1, pv2))) ictx
| inDataNull ish d pv1 pv2 dsh vals osh d' md' pv1' =>
       !!(isptr ictx /\ isptr octx /\ readable_share ish /\ isptr d /\ 
          readable_share dsh /\ writable_share osh /\ pv1=nullval /\ is_pointer_or_null pv2)
       && EVP_MD_CTX_NNnode ish (d, (nullval, (pv1, pv2))) ictx *
          data_at dsh (Tstruct _env_md_st noattr) vals d * 
          EVP_MD_CTX_NNnode osh (d', (md', (pv1', nullval))) octx *
          if orb (Val.eq d' nullval) (Val.eq d d') 
          then EX ctxsz:_, !!(get_ctxsize vals = Vint ctxsz /\ Int.eq ctxsz Int.zero=false)&&emp  
          else EX dsh':_, EX vals':_, EX ctxsz': _,
               !!(readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz' /\ Int.eq ctxsz' Int.zero = false) 
               && data_at dsh' (Tstruct _env_md_st noattr) vals' d' *
                  ((!!(md' = nullval)&& emp) || memory_block Tsh (Int.unsigned ctxsz') md')
| equalDigests_outDataNull ish d md pv1 pv2 dsh vals osh pv1' imdsh idata ctxsz =>
       !!(isptr ictx /\ isptr octx /\ readable_share ish /\ isptr d /\ 
          readable_share dsh /\ writable_share osh /\ isptr md /\ readable_share imdsh /\
          pv1=nullval /\ is_pointer_or_null pv2 /\
          get_ctxsize vals = Vint ctxsz /\ 4 <= Int.unsigned ctxsz <= Int.max_unsigned)
       && EVP_MD_CTX_NNnode ish (d, (md, (pv1, pv2))) ictx *
          data_at dsh (Tstruct _env_md_st noattr) vals d * 
          EVP_MD_CTX_NNnode osh (d, (nullval, (pv1', nullval))) octx *
          data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md
| equalDigests_outDataPtr ish d md pv1 pv2 dsh vals osh pv1' imdsh idata ctxsz md' =>
       !!(isptr ictx /\ isptr octx /\ readable_share ish /\ isptr d /\ 
          readable_share dsh /\ writable_share osh /\ isptr md /\ readable_share imdsh /\
          pv1=nullval /\ is_pointer_or_null pv2 /\
          get_ctxsize vals = Vint ctxsz /\ 4 <= Int.unsigned ctxsz <= Int.max_unsigned /\
          isptr md')
       && EVP_MD_CTX_NNnode ish (d, (md, (pv1, pv2))) ictx *
          data_at dsh (Tstruct _env_md_st noattr) vals d * 
          EVP_MD_CTX_NNnode osh (d, (md', (pv1', nullval))) octx *
          data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
          memory_block Tsh (Int.unsigned ctxsz) md'
| outDigest_Null ish d md pv1 pv2 dsh vals osh md' pv1' imdsh idata ctxsz =>
       !!(isptr ictx /\ isptr octx /\ readable_share ish /\ isptr d /\ 
          readable_share dsh /\ writable_share osh /\ isptr md /\ readable_share imdsh /\
          pv1=nullval /\ is_pointer_or_null pv2 /\
          get_ctxsize vals = Vint ctxsz /\ 4 <= Int.unsigned ctxsz <= Int.max_unsigned)
       && EVP_MD_CTX_NNnode ish (d, (md, (pv1, pv2))) ictx *
          data_at dsh (Tstruct _env_md_st noattr) vals d * 
          EVP_MD_CTX_NNnode osh (nullval, (md', (pv1', nullval))) octx *
          data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md

| distinctDigests ish d md pv1 pv2 dsh vals osh d' md' pv1' imdsh idata ctxsz dsh' vals' ctxsz' =>
       !!(isptr ictx /\ isptr octx /\ readable_share ish /\ isptr d /\ 
          readable_share dsh /\ writable_share osh /\ isptr md /\ readable_share imdsh /\
          pv1=nullval /\ is_pointer_or_null pv2 /\
          get_ctxsize vals = Vint ctxsz /\ 4 <= Int.unsigned ctxsz <= Int.max_unsigned /\
          d<>d' /\
          get_ctxsize vals' = Vint ctxsz' /\ Int.eq ctxsz' Int.zero = false)
       && EVP_MD_CTX_NNnode ish (d, (md, (pv1, pv2))) ictx *
          data_at dsh (Tstruct _env_md_st noattr) vals d * 
          EVP_MD_NNnode dsh' vals' d' *
          EVP_MD_CTX_NNnode osh (d', (md', (pv1', nullval))) octx *
          data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
          ((!!(md' = nullval)&& emp) || memory_block Tsh (Int.unsigned ctxsz') md')
end.

Definition POST3 ictx octx ish d  pv2 (*dsh*) (vals:reptype (Tstruct _env_md_st noattr)) osh d' (*md' pv1' idsh idata*) rv:mpred :=
!!(rv=Vint Int.one) &&
match vals with (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) =>
(if orb (Val.eq d' nullval) (Val.eq d d')
 then
  EX ctxsz : int,
  !! (get_ctxsize (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) = Vint ctxsz /\ Int.eq ctxsz Int.zero = false) && emp
 else
  EX dsh' : share,
  (EX vals' : reptype (Tstruct _env_md_st noattr),
   (EX ctxsz' : int,
    !! (readable_share dsh' /\
        get_ctxsize vals' = Vint ctxsz' /\
        Int.eq ctxsz' Int.zero = false) &&
    data_at dsh' (Tstruct _env_md_st noattr) vals' d'))) * 
(EVP_MD_node
   (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) d) *
(data_at osh (Tstruct _env_md_ctx_st noattr)
   (d,
   (Vundef,
   (Vundef,
   force_val
     (sem_cast (tptr (Tstruct _evp_md_pctx_ops noattr))
        (tptr (Tstruct _evp_md_pctx_ops noattr)) pv2)))) octx) *
(data_at ish (Tstruct _env_md_ctx_st noattr)
   (d, (nullval, (nullval, pv2))) ictx)
end.

Definition POST4 ictx octx rv ish d md pv2 dsh vals osh imdsh idata ctxsz:mpred :=
(!!(rv=Vint Int.zero)
 && (data_at osh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (Vundef, Vundef))) octx *
     data_at dsh (Tstruct _env_md_st noattr) vals d *
     data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
     data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx))
||
( !!(rv=Vint Int.one)
  && (EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) &&
    data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m *
    data_at osh (Tstruct _env_md_ctx_st noattr) (d, (m, (Vundef, pv2))) octx *
    data_at dsh (Tstruct _env_md_st noattr) vals d *
    data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
    data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx)).

Definition POST5 (ictx octx rv:val) (ish:share) (d md pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (pv1': val)
                      (imdsh:share) (idata:list int) (ctxsz: int)
                      (md':val): mpred :=
!!(rv=Vint Int.one)
&& data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md' *
   data_at osh (Tstruct _env_md_ctx_st noattr) (d, (md', (Vundef, pv2))) octx *
   data_at dsh (Tstruct _env_md_st noattr) vals d *
   data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
   data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx.

Definition POST6 (ictx octx rv:val) (ish:share) (d md pv1 pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (md' pv1': val)
                      (imdsh:share) (idata:list int) (ctxsz: int): mpred :=
(!!(rv=Vint Int.zero)
 && (data_at osh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (Vundef, Vundef))) octx *
     data_at dsh (Tstruct _env_md_st noattr) vals d *
     data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
     data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx))
||
!!(rv=Vint Int.one)
&& EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) &&
   data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m *
   data_at osh (Tstruct _env_md_ctx_st noattr) (d, (m, (Vundef, pv2))) octx *
   data_at dsh (Tstruct _env_md_st noattr) vals d *
   data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
   data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx.

Definition POST7 (ictx octx rv:val) (ish:share) (d md pv1 pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (d' md' pv1': val)
                      (imdsh:share) (idata:list int) (ctxsz: int)
                      (dsh':share)(vals' : reptype (Tstruct _env_md_st noattr))(ctxsz':int): mpred :=
(!!(rv=Vint Int.zero)
 && (data_at osh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (Vundef, Vundef))) octx *
     data_at dsh (Tstruct _env_md_st noattr) vals d *
     EVP_MD_NNnode dsh' vals' d' *
     data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
     data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx))
||
!!(rv=Vint Int.one)
&& EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) &&
   data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m *
   data_at osh (Tstruct _env_md_ctx_st noattr) (d, (m, (Vundef, pv2))) octx * 
   EVP_MD_NNnode dsh' vals' d' *
   data_at dsh (Tstruct _env_md_st noattr) vals d *
   data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
   data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx.

Definition copyExPost (c: copyEx_cases) (ictx octx:val) rv : mpred := 
match c with
   ictxNull => !!(rv=Vint Int.zero) && emp
| inDigestNull ish md pv1 pv2 => !!(rv=Vint Int.zero) && data_at ish (Tstruct _env_md_ctx_st noattr) (nullval, (md, (pv1, pv2))) ictx
| inDataNull ish d pv1 pv2 dsh vals osh d' md' pv1' => POST3 ictx octx ish d  pv2 (*dsh*) vals osh d' rv
| equalDigests_outDataNull ish d md pv1 pv2 dsh vals osh pv1' imdsh idata ctxsz => 
    POST4 ictx octx rv ish d md pv2 dsh vals osh imdsh idata ctxsz
| equalDigests_outDataPtr ish d md pv1 pv2 dsh vals osh pv1' imdsh idata ctxsz md' => 
    POST5 ictx octx rv ish d md pv2 dsh vals osh pv1' imdsh idata ctxsz md'
| outDigest_Null ish d md pv1 pv2 dsh vals osh md' pv1' imdsh idata ctxsz  =>
    POST6 ictx octx rv ish d md pv1 pv2 dsh vals osh md' pv1' imdsh idata ctxsz
| distinctDigests ish d md pv1 pv2 dsh vals osh d' md' pv1' imdsh idata ctxsz dsh' vals' ctxsz' =>
    POST7 ictx octx rv ish d md pv1 pv2 dsh vals osh d' md' pv1' imdsh idata ctxsz dsh' vals' ctxsz'
end.

Definition EVP_MD_CTX_copy_ex_SPEC := DECLARE _EVP_MD_CTX_copy_ex
  WITH ep: val, octx:val, ictx:val, case:copyEx_cases
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP ()
      LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
      SEP (ERR ep; copyExPre case ictx octx)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERR ep; copyExPost case ictx octx rv).

Inductive copy_cases :=
  cp_ictxNull: copy_cases
| cp_inDigestNull: forall (ish:share) (md pv1 pv2 :val), copy_cases
| cp_inDataNull: forall (ish:share) (d pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr)), copy_cases
| cp_default: forall (ish:share) (d md pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (imdsh:share) (idata:list int) (ctxsz: int), copy_cases.

Definition copyPre (c:copy_cases) (ictx octx:val) : mpred :=
match c with 
  cp_ictxNull => !!(ictx=nullval)&&emp
| cp_inDigestNull ish md pv1 pv2 => !!(isptr ictx /\ readable_share ish)
                            && EVP_MD_CTX_NNnode ish (nullval, (md, (pv1, pv2))) ictx
| cp_inDataNull ish d pv2 dsh vals =>
       !!(readable_share ish /\ readable_share dsh /\ is_pointer_or_null pv2 /\
          exists ctxsz, get_ctxsize vals = Vint ctxsz /\ Int.eq ctxsz Int.zero=false)
       && EVP_MD_CTX_NNnode ish (d, (nullval, (nullval, pv2))) ictx *
          data_at dsh (Tstruct _env_md_st noattr) vals d 
| cp_default ish d md pv2 dsh vals imdsh idata ctxsz =>
       !!(readable_share ish /\ readable_share dsh /\ 
          is_pointer_or_null pv2 /\ readable_share imdsh /\
          get_ctxsize vals = Vint ctxsz /\ 4 <= Int.unsigned ctxsz <= Int.max_unsigned)
       && EVP_MD_CTX_NNnode ish (d, (md, (nullval, pv2))) ictx *
          data_at dsh (Tstruct _env_md_st noattr) vals d * 
          data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md
end.

Definition copyPost (c:copy_cases) (ictx octx rv:val) osh : mpred :=
match c with 
  cp_ictxNull => 
    !!(rv=nullval) 
    && data_at osh (tarray tuchar 16) (list_repeat 16 (Vint Int.zero)) octx
| cp_inDigestNull ish md pv1 pv2 => 
    !!(rv=nullval) 
    && data_at osh (tarray tuchar 16) (list_repeat 16 (Vint Int.zero)) octx *
    data_at ish (Tstruct _env_md_ctx_st noattr) (nullval, (md, (pv1, pv2))) ictx
| cp_inDataNull ish d pv2 dsh vals =>
    !!(rv=Vint Int.one) 
    && EVP_MD_node vals d *
       data_at osh (Tstruct _env_md_ctx_st noattr)
         (d, (Vundef, (Vundef, pv2))) octx *
       data_at ish (Tstruct _env_md_ctx_st noattr)
        (d, (nullval, (nullval, pv2))) ictx
| cp_default ish d md pv2 dsh vals imdsh idata ctxsz => 
  POST6 ictx octx rv ish d md nullval pv2 dsh vals osh nullval
  nullval imdsh idata ctxsz
end.

(*since init is called, octx must not be null!*)
Definition EVP_MD_CTX_copy_SPEC := DECLARE _EVP_MD_CTX_copy
  WITH ep: val, octx:val, ictx:val, osh:share, case:copy_cases
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (writable_share osh)
      LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
      SEP (ERR ep; data_at_ osh (Tstruct _env_md_ctx_st noattr) octx; 
           copyPre case ictx octx)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERR ep; copyPost case ictx octx rv osh).

Definition Gprog_copy : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [EVP_MD_CTX_init_SPEC; EVP_MD_CTX_copy_SPEC; EVP_MD_CTX_copy_ex_SPEC].

Lemma body_EVP_MD_CTX_copy: semax_body Vprog Gprog_copy f_EVP_MD_CTX_copy EVP_MD_CTX_copy_SPEC.
Proof. 
  start_function. 
  assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] octx) as FCO by entailer!.
  forward_call (octx, osh, (sizeof (Tstruct _env_md_ctx_st noattr))).
  destruct case; simpl; normalize.
+ forward_call (ep, octx, nullval, ictxNull). simpl; entailer!.
  Intros v. forward. Exists nullval; entailer!.
+ forward_call (ep, octx, ictx, inDigestNull ish md pv1 pv2). simpl; entailer!.
  Intros v. forward. Exists nullval; entailer!.
+ assert_PROP (isptr d) by entailer!.
  replace_SEP 2 (data_at osh (Tstruct _env_md_ctx_st noattr)
      (nullval, (nullval, (nullval, nullval))) octx).
  { (*holds because of FCout*) entailer.
    unfold_data_at 2%nat. simpl. at 2. erewrite field_at_Tarray.
     3: simpl.
     admit. (*eapply derives_trans. apply data_at_memory_block. simpl. *) }
  (*unfold data_at_, field_at_. simpl. unfold default_val.x simpl. *)
  forward_call (ep, octx, ictx, inDataNull ish d nullval pv2 dsh vals osh nullval nullval nullval).
  simpl. entailer!. simpl. destruct H2 as [ctxsz [H2a Hb2]]. Exists ctxsz. entailer. cancel. 
  Intros v. forward. unfold POST3. 
  destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
  simpl in type, mds, flags,ini, upd, fin, ctxsize, blsize.
  destruct (Val.eq nullval nullval); [simpl | solve [ congruence ]].
  Intros ctxsz. Exists (Vint v); entailer!. cancel.
+ replace_SEP 3 (data_at osh (Tstruct _env_md_ctx_st noattr)
      (nullval, (nullval, (nullval, nullval))) octx).
  { admit. (*see previous case*) }
  forward_call (ep, octx, ictx, 
                outDigest_Null ish d md nullval pv2 dsh vals osh nullval nullval imdsh idata ctxsz).
  { simpl. entailer!. } 
  Intros v. forward. Exists (Vint v); entailer!. 
Admitted.

Definition Gprog_copy_ex : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [OPENSSL_memcpy_SPEC; OPENSSL_PUT_ERROR_SPEC; OPENSSL_malloc_SPEC; EVP_MD_CTX_cleanup_SPEC4].

Lemma body_EVP_MD_CTX_copy_ex: semax_body Vprog Gprog_copy_ex f_EVP_MD_CTX_copy_ex EVP_MD_CTX_copy_ex_SPEC.
Proof. 
  start_function. forward. destruct case; simpl; normalize.
+ (*Case 1: ictxNull*)
  forward_if (PROP ( )
   LOCAL (gvar ___stringlit_1 ep; temp _t'1 (Vint Int.one); temp _tmp_buf (Vint (Int.repr 0));
          temp _out octx; temp _in nullval)  
   SEP (ERR ep)); [ clear H; forward; entailer! | inv H | ] .

  forward_if (PROP (False) LOCAL () SEP()); [ clear H | inv H | Intros; contradiction]. 
  forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.repr 100),
                ep, Vint (Int.repr 121)).
  forward. Exists nullval. entailer!. 
+ (*Case 2: indigestNull*)
  rename H into ISH.
  forward_if (
   PROP ( )
   LOCAL (gvar ___stringlit_1 ep; temp _t'1 (Vint Int.one); temp _t'26 nullval;
          temp _tmp_buf (Vint (Int.repr 0)); temp _out octx; temp _in ictx)
   SEP (ERR ep; data_at ish (Tstruct _env_md_ctx_st noattr) (nullval, (md, (pv1, pv2)))
          ictx)); [ subst; contradiction | forward; forward; entailer! | ]. 
  deadvars!.
  
  forward_if (PROP (False) LOCAL () SEP()); [ | inv H | Intros; contradiction].
  forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.repr 100),
                ep, Vint (Int.repr 121)).
  forward. Exists nullval. entailer!. 
+ (*Case 3: indataNull *)
  rename H into ISH. rename H0 into DSH. rename H1 into OSH.
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _t'1 (Vint Int.zero); temp _t'26 d;
           temp _tmp_buf (Vint (Int.repr 0)); temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at ish (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d;
         data_at osh (Tstruct _env_md_ctx_st noattr) (d', (md', (pv1', nullval))) octx;
         if orb (Val.eq d' nullval) (Val.eq d d')
         then EX ctxsz:_, !!(get_ctxsize vals = Vint ctxsz /\ Int.eq ctxsz Int.zero=false)&&emp  
         else EX dsh':_, EX vals':_, EX ctxsz': _,
               !!(readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz' /\ Int.eq ctxsz' Int.zero = false) 
               && data_at dsh' (Tstruct _env_md_st noattr) vals' d' *
                 ((!!(md' = nullval)&& emp) || memory_block Tsh (Int.unsigned ctxsz') md'))).
  { subst; contradiction. }
  { freeze [2;3;4] FR1. forward. forward. thaw FR1. entailer!. destruct d; try contradiction; trivial. }
  deadvars!.
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _tmp_buf (Vint (Int.repr 0));
           temp _out octx; temp _in ictx)
    SEP (ERR ep;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d;
         data_at osh (Tstruct _env_md_ctx_st noattr) (d', (md', (pv1', nullval))) octx;
         if orb (Val.eq d' nullval) (Val.eq d d') then EX ctxsz:_, !!(get_ctxsize vals = Vint ctxsz /\ Int.eq ctxsz Int.zero=false)&&emp  
         else EX dsh':_, EX vals':_, EX ctxsz': _,
              !!(readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz' /\ Int.eq ctxsz' Int.zero = false) 
              && data_at dsh' (Tstruct _env_md_st noattr) vals' d' *
                 ((!!(md' = nullval)&& emp) || memory_block Tsh (Int.unsigned ctxsz') md'))).
   { elim H; trivial. }
   { clear H. forward. entailer!. }
   freeze [4] FR1. forward. 
   forward.
   forward_if (
     PROP ( )
     LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx;
            temp _tmp_buf (if Val.eq d d' then md' else Vint (Int.repr 0)))
     SEP (ERR ep;
          data_at ish (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, pv2))) ictx;
          data_at dsh (Tstruct _env_md_st noattr) vals d; FRZL FR1;
          data_at osh (Tstruct _env_md_ctx_st noattr) (d', (if Val.eq d d' then nullval else md', (pv1', nullval))) octx)).
   { clear H. destruct d; try contradiction.
     apply denote_tc_test_eq_split.
     + destruct (Val.eq (Vptr b i) d'); subst.
       - apply sepcon_valid_pointer1.
         apply sepcon_valid_pointer2. entailer!.
       - thaw FR1. destruct (Val.eq d' nullval); subst; [ solve [apply valid_pointer_null] | simpl ]. 
         Intros dsh' vals' ctxsz'.
         apply sepcon_valid_pointer1. 
         apply sepcon_valid_pointer1. 
         apply sepcon_valid_pointer1. 
         apply sepcon_valid_pointer1. clear -H. entailer!.
     + apply sepcon_valid_pointer1.
       apply sepcon_valid_pointer2. entailer!. }
   { unfold typed_true, sem_cmp_pp in H. forward.
     destruct (Val.eq d d'); subst; simpl in H.
     + forward. entailer!.
     + destruct d; try contradiction. destruct d'; try contradiction; simpl in H.
       destruct (Int.eq i0 Int.zero); simpl in H; inv H.
       destruct (eq_block b0 b); subst; simpl in H.
       - destruct (Int.eq_dec i0 i); subst; simpl in H. elim n; trivial.
         rewrite Int.eq_false in H; trivial; inv H.
       - inv H. }
   { unfold typed_true, sem_cmp_pp in H. 
     destruct (Val.eq d d'); subst; simpl in H.
     + destruct d'; try contradiction. simpl in H.
       rewrite if_true, Int.eq_true in H; trivial. inv H.
     + forward. entailer!. }
   
   (*Line 133: cleanup*)
   thaw FR1.
   assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] octx) as FCout by entailer!.

   assert (exists auxvals:reptype (Tstruct _env_md_ctx_st noattr), auxvals=(d, (nullval, (nullval, pv2)))).
   { eexists; reflexivity. }
   destruct H as [auxvals AUXVALS].
   eapply semax_seq with (Q:=
     PROP ( )
     LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx;
            temp _tmp_buf (if Val.eq d d' then md' else Vint (Int.repr 0))) 
     SEP (ERR ep; EVP_MD_node vals d;
          data_at_ osh (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr))) octx; 
          if orb (Val.eq d' nullval) (Val.eq d d')
          then EX ctxsz : int,
               !! (get_ctxsize vals = Vint ctxsz /\ Int.eq ctxsz Int.zero = false) && emp
          else EX dsh' : share,
               EX vals' : reptype (Tstruct _env_md_st noattr),
               EX ctxsz' : int, !! (readable_share dsh' /\
                                    get_ctxsize vals' = Vint ctxsz' /\
                                    Int.eq ctxsz' Int.zero = false)
                  && data_at dsh' (Tstruct _env_md_st noattr) vals' d';
                     data_at ish (Tstruct _env_md_ctx_st noattr) auxvals ictx)).
   { destruct (Val.eq d' nullval); subst.
     { simpl; Intros ctxsz. rename H into ctxszH1. rename H0 into ctxszH2.  
       rewrite ! if_false. 2: destruct d; try contradiction; discriminate. 2: destruct d; try contradiction; discriminate.
       forward_call (octx, osh, md', pv1', 
         @inl unit (share * val * (reptype (Tstruct _env_md_st noattr))) tt).
       { unfold EVP_MD_CTX_NNnode. entailer!. }
       entailer!. Exists ctxsz. entailer!. apply orp_right2. Exists dsh; unfold EVP_MD_NNnode. entailer!.
     } 
     rewrite orb_false_l.
     destruct (Val.eq d d'); subst; simpl.
     - Intros ctxsz. rename H into ctxszH1. rename H0 into ctxszH2.  
       forward_call (octx, osh, nullval, pv1', 
         @inr unit (share * val * (reptype (Tstruct _env_md_st noattr))) (dsh, d', vals)).
       { Exists ctxsz. 
         assert (FR: Frame = [ERR ep; data_at ish (Tstruct _env_md_ctx_st noattr) (d', (nullval, (nullval, pv2))) ictx]); subst Frame. reflexivity.
         clear FR. simpl. unfold EVP_MD_NNnode. entailer!. apply orp_right1; trivial. }
       Exists ctxsz; entailer. cancel. apply orp_right2. Exists dsh. trivial. 
     - Intros dsh' vals' ctxsz'.
       rename H into DSH'. rename H0 into ctxszH1'. rename H1 into ctxszH2'. 
       rewrite data_at_isptr with (p:=d'). Intros. 
       freeze [0;1;2] FR2.
       forward_call (octx, osh, md', pv1', 
         @inr unit (share * val * (reptype (Tstruct _env_md_st noattr))) (dsh', d', vals')).
       { Exists ctxsz'.
         assert (FR: Frame = [FRZL FR2]) (*data_at dsh (Tstruct _env_md_st noattr) vals d; 
                   data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (pv1, pv2))) ictx])*); subst Frame. reflexivity.
         clear FR. simpl. unfold EVP_MD_NNnode. entailer!. }
       unfold EVP_MD_node, EVP_MD_NNnode. entailer!. Exists dsh' vals' ctxsz'. thaw FR2.
       cancel. 
       rewrite distrib_orp_sepcon. apply orp_right2. Exists dsh. normalize. cancel. }

  unfold MORE_COMMANDS, abbreviate; subst auxvals. forward.
  replace_SEP 2 (data_at_ osh (Tstruct _env_md_ctx_st noattr) octx).
  { (*holds because of FCout*) rewrite 2 data_at__memory_block. entailer!. }
  forward. simpl. replace (force_val (sem_cast_neutral d)) with d by (destruct d; try contradiction; trivial).

  (*line 136: read in->md_data && in->digest->ctx_size*)
  forward. 
  freeze [3] FR1.
  destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
  simpl in type, mds, flags,ini, upd, fin, ctxsize, blsize. 
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _t'3 nullval; temp _t'20 nullval; temp _t'23 d;
           temp _tmp_buf (if Val.eq d d' then md' else Vint (Int.repr 0));
           temp _out octx; temp _in ictx)
    SEP (ERR ep; FRZL FR1; EVP_MD_node (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) d;
         field_at osh (Tstruct _env_md_ctx_st noattr) [] (d, (Vundef, (Vundef, Vundef))) octx;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, pv2))) ictx)).
  { inv H. }
  { clear H. forward. entailer!. }
  deadvars!.
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx; 
           temp _tmp_buf (if Val.eq d d' then md' else Vint (Int.repr 0)))
    SEP (ERR ep; FRZL FR1;
         EVP_MD_node (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) d;
         field_at osh (Tstruct _env_md_ctx_st noattr) [] (d, (Vundef, (Vundef, Vundef))) octx;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, pv2))) ictx)).
   { elim H; trivial. }
   { clear H. forward; entailer!. }

  forward. 
  freeze [0;1;2] FR2.
  forward. freeze [0;1] FR3. forward. freeze [0;1] FR4.

  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _t'5 nullval; temp _t'12 pv2;
           temp _tmp_buf (if Val.eq d d' then md' else Vint (Int.repr 0));
           temp _out octx; temp _in ictx)  SEP (FRZL FR4)). 
   { inv H. }
   { clear H. forward. entailer!. }

  deadvars!.
  forward_if 
    (PROP ( ) LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx) SEP (FRZL FR4)).
  {  elim H; trivial. }
  { clear H. forward. entailer!. }

  forward. Exists (Vint Int.one). entailer!. thaw FR4. thaw FR3. thaw FR2.
  cancel. unfold POST3. apply andp_right; [ apply prop_right; trivial | ].
  thaw FR1. clear.
  rewrite ! sepcon_assoc.
  apply sepcon_derives; [trivial | cancel].

+ (*Case 4: equalDigests_outDataNull *)
  rename H into ISH. rename H0 into DSH. rename H1 into OSH. rename H2 into IMDSH.
  rename H3 into cxtszH1. rename H4 into ctxszH2. clear PNd PNmd.
  assert (ctxszH3: Int.eq ctxsz Int.zero=false).
  { remember (Int.eq ctxsz Int.zero) as q. destruct q; trivial.
    apply binop_lemmas2.int_eq_true in Heqq; subst. rewrite Int.unsigned_zero in *. omega. } 
  freeze [2;3;4] FR1.
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _t'1 (Vint Int.zero); 
           temp _tmp_buf (Vint (Int.repr 0)); temp _out octx; temp _in ictx)
    SEP (FRZL FR1;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)).  
  { subst; contradiction. }
  { clear H. forward. destruct d; try contradiction. forward. entailer!. }

  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _tmp_buf (Vint (Int.repr 0));
           temp _out octx; temp _in ictx)
    SEP (FRZL FR1;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)).
  { elim H; trivial. }
  { clear H. forward. entailer!. }

  thaw FR1. forward. forward.
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _tmp_buf nullval;
           temp _out octx; temp _in ictx)
    SEP (ERR ep; 
         data_at osh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (pv1', nullval))) octx;
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)).
  { clear H. forward. forward. entailer!. }
  { destruct d; try contradiction. unfold sem_cmp_pp in H; simpl in H.
    rewrite if_true, Int.eq_true in H; trivial; inv H. }
   
  (*Line 133: cleanup*)
  assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] octx) as FCout by entailer!.

  forward_call (octx, osh, nullval, pv1', 
         @inr unit (share * val * (reptype (Tstruct _env_md_st noattr))) (dsh, d, vals)).
  { Exists ctxsz. 
    assert (FR: Frame = [ERR ep;
                         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
                         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx]); subst Frame. reflexivity.
    clear FR. simpl. unfold EVP_MD_NNnode; entailer!. apply orp_right1; trivial. }

  (*line 136: read in->md_data && in->digest->ctx_size*)
  forward.
  replace_SEP 0 (data_at_ osh (Tstruct _env_md_ctx_st noattr) octx).
  { (*holds because of FCout*) rewrite 2 data_at__memory_block. entailer!. }
  forward. simpl. replace (force_val (sem_cast_neutral d)) with d by (destruct d; try contradiction; trivial).

  forward. 
  freeze [0;2] FR1.
  destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
  simpl in type, mds, flags,ini, upd, fin, ctxsize, blsize.
  deadvars!. simpl in *.
  unfold EVP_MD_NNnode; Intros. 
  destruct d; simpl in Pd; try contradiction. 
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _t'3 (Vint Int.one); temp _t'20 md; 
           temp _tmp_buf nullval; temp _out octx; temp _in ictx)
    SEP (FRZL FR1;
         data_at dsh (Tstruct _env_md_st noattr)
          (type,
          (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz)))))))
          (Vptr b i);
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (Vptr b i, (md, (nullval, pv2))) ictx)).
  { clear H.
    apply denote_tc_test_eq_split.
     + apply sepcon_valid_pointer1.
       apply sepcon_valid_pointer2. apply data_at_valid_ptr. intuition.
       simpl. rewrite Z.mul_1_l, Z.max_r; trivial. omega. apply Int.unsigned_range. 
     + apply valid_pointer_null. }
  { simpl in *. clear H.
    forward. forward. forward. entailer!. simpl. rewrite ctxszH3; trivial. }
  { subst; contradiction. } 
  thaw FR1. 
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; 
           temp _tmp_buf nullval; temp _out octx; temp _in ictx)
    SEP (EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) && 
                 (data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m *
                  field_at osh (Tstruct _env_md_ctx_st noattr) []
                    (Vptr b i, (m, (Vundef, Vundef))) octx);
         ERR ep;  
         data_at dsh (Tstruct _env_md_st noattr) (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) (Vptr b i);
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (Vptr b i, (md, (nullval, pv2))) ictx)).
  2: solve [inv H].
  { clear H Pd.
    forward_if (
      PROP ( )
      LOCAL (gvar ___stringlit_1 ep; 
        temp _tmp_buf nullval; temp _out octx; temp _in ictx)
      SEP (EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) && 
                 (memory_block Tsh (Int.unsigned ctxsz)  m *
                   field_at osh (Tstruct _env_md_ctx_st noattr) []
                    (Vptr b i, (m, (Vundef, Vundef))) octx);
           ERR ep;  
           data_at dsh (Tstruct _env_md_st noattr) (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) (Vptr b i);
           data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
           data_at ish (Tstruct _env_md_ctx_st noattr) (Vptr b i, (md, (nullval, pv2))) ictx)).
    { contradiction. }
    { clear H. forward. forward.
      forward_call (Int.unsigned ctxsz).
       + rewrite Int.repr_unsigned; simpl. entailer!.
       + Intros m. forward. forward.
         freeze [1;3;4;5] FR1. focus_SEP 1.
         apply semax_orp_SEPx.
         - normalize. 
           forward_if (PROP (False) LOCAL () SEP ()). 
           * clear H.
             forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                ep, Vint (Int.repr 142)). 
             forward. Exists nullval. thaw FR1; entailer!.
             apply orp_right1. entailer!. 
           * inv H. 
           * intros. unfold overridePost. old_go_lower. clear H.
             destruct (EqDec_exitkind ek EK_normal). entailer!. trivial.
         - normalize. assert_PROP (isptr m) as Hm by entailer!.
           destruct m; try contradiction. simpl.
           forward_if (
              PROP ( )
              LOCAL (gvar ___stringlit_1 ep; temp _t'17 (Vptr b0 i0); temp _t'2 (Vptr b0 i0);
                     temp _t'19 (Vint ctxsz); temp _t'18 (Vptr b i);
                     temp _t'3 (Vint Int.one); temp _t'20 md; 
                     temp _tmp_buf nullval; temp _out octx; temp _in ictx)
              SEP (ERR ep; memory_block Tsh (Int.unsigned ctxsz)  (Vptr b0 i0); FRZL FR1)). 
           { clear H0. apply denote_tc_test_eq_split; try apply valid_pointer_null.
             apply sepcon_valid_pointer1.  
             apply sepcon_valid_pointer1.  
             apply memory_block_valid_ptr. intuition. omega. }
           { elim H0; trivial. }
           { forward. entailer!.  }
           unfold POSTCONDITION, abbreviate, overridePost; intros.
           destruct (EqDec_exitkind ek EK_normal). 
           * subst; old_go_lower. entailer!. thaw FR1. Exists  (Vptr b0 i0); entailer!.   
           * old_go_lower. clear H0. rewrite ! if_false; trivial. }
    Intros m. rename H into M. forward. forward. forward. forward.
    (*memcpy*)
    forward_call ((imdsh,Tsh),m, md,Int.unsigned ctxsz, idata).
         { rewrite Int.repr_unsigned; entailer!. }
         { simpl. cancel. }
         { simpl; split; trivial. split; trivial. apply Int.unsigned_range_2. }
    entailer!. Exists m. entailer!. }
  Intros m. rename H into M. forward. forward. forward. 
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _t'5 nullval; temp _out octx; temp _in ictx)
    SEP (ERR ep;
         data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m;
         field_at osh (Tstruct _env_md_ctx_st noattr) []
           (Vptr b i, (m, (Vundef,
              force_val
               (sem_cast (tptr (Tstruct _evp_md_pctx_ops noattr))
                (tptr (Tstruct _evp_md_pctx_ops noattr)) pv2)))) octx;
         data_at dsh (Tstruct _env_md_st noattr)
           (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) (Vptr b i);
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (Vptr b i, (md, (nullval, pv2))) ictx)).
     { contradiction. }
     { forward; entailer!. } 
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m;
         field_at osh (Tstruct _env_md_ctx_st noattr) []
          (Vptr b i, (m, (Vundef,
             force_val
              (sem_cast (tptr (Tstruct _evp_md_pctx_ops noattr))
               (tptr (Tstruct _evp_md_pctx_ops noattr)) pv2)))) octx;
         data_at dsh (Tstruct _env_md_st noattr)
           (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) (Vptr b i);
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (Vptr b i, (md, (nullval, pv2))) ictx)). 
     { elim H; trivial. }
     { forward; entailer!. }
  forward. Exists (Vint Int.one); entailer!.
  apply orp_right2. Exists m. entailer!. 

+ (*Case 5: equalDigests_outDataPtr *)
  rename H into ISH. rename H0 into DSH. rename H1 into OSH. rename H2 into IMDSH.
  rename H3 into cxtszH1. rename H4 into ctxszH2. clear PNd PNmd.
  assert (ctxszH3: Int.eq ctxsz Int.zero=false).
  { remember (Int.eq ctxsz Int.zero) as q. destruct q; trivial.
    apply binop_lemmas2.int_eq_true in Heqq; subst. rewrite Int.unsigned_zero in *. omega. } 
  freeze [4] MD'.
  freeze [0;3;4;5] FR1.
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _t'1 (Vint Int.zero); 
           temp _tmp_buf (Vint (Int.repr 0)); temp _out octx; temp _in ictx)
    SEP (FRZL FR1;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)).  
  { subst; contradiction. }
  { clear H. forward. destruct d; try contradiction. forward. entailer!.  }

  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _tmp_buf (Vint (Int.repr 0)); 
           temp _out octx; temp _in ictx)
    SEP (FRZL FR1;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)).
  { elim H; trivial. }
  { clear H. forward. entailer!. }

  thaw FR1. forward. forward.
  forward_if 
  (PROP ( )
   LOCAL (gvar ___stringlit_1 ep; temp _tmp_buf md'; temp _out octx; temp _in ictx)
   SEP (ERR ep; FRZL MD';
   data_at osh (Tstruct _env_md_ctx_st noattr)
     (d, (nullval, (pv1', nullval))) octx;
   data_at imdsh (tarray tuchar (Int.unsigned ctxsz))
     (map Vint idata) md;
   data_at ish (Tstruct _env_md_ctx_st noattr)
     (d, (md, (nullval, pv2))) ictx;
   data_at dsh (Tstruct _env_md_st noattr) vals d)). 
  { clear H. forward. forward. entailer!. }
  { destruct d; try contradiction. unfold sem_cmp_pp in H; simpl in H.
    rewrite if_true, Int.eq_true in H; trivial; inv H. }
   
  (*Line 133: cleanup*)
  assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] octx) as FCout by entailer!.

  forward_call (octx, osh, nullval, pv1', 
         @inr unit (share * val * (reptype (Tstruct _env_md_st noattr))) (dsh, d, vals)).
  { Exists ctxsz. 
    assert (FR: Frame = [ERR ep; FRZL MD'; 
                         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
                         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx]); subst Frame. reflexivity.
    clear FR. simpl. unfold EVP_MD_NNnode; entailer!. apply orp_right1; trivial. }

  (*line 136: read in->md_data && in->digest->ctx_size*)
  forward.
  replace_SEP 0 (data_at_ osh (Tstruct _env_md_ctx_st noattr) octx).
  { (*holds because of FCout*) rewrite 2 data_at__memory_block. entailer!. }
  forward. simpl. replace (force_val (sem_cast_neutral d)) with d by (destruct d; try contradiction; trivial).

  forward. 
  freeze [0;3] FR1.
  destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
  simpl in type, mds, flags,ini, upd, fin, ctxsize, blsize.
  deadvars!. simpl in *.
  unfold EVP_MD_NNnode; Intros. 
  destruct d; simpl in Pd; try contradiction. 
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _t'3 (Vint Int.one);
           temp _t'20 md; temp _tmp_buf md'; temp _out octx; temp _in ictx)
   SEP (ERR ep; FRZL FR1; 
        data_at dsh (Tstruct _env_md_st noattr)
          (type,
          (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz)))))))
          (Vptr b i);
       data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
       data_at ish (Tstruct _env_md_ctx_st noattr) (Vptr b i, (md, (nullval, pv2))) ictx)).
  { clear H.
    apply denote_tc_test_eq_split.
     + apply sepcon_valid_pointer1.
       apply sepcon_valid_pointer2. apply data_at_valid_ptr. intuition.
       simpl. rewrite Z.mul_1_l, Z.max_r; trivial. omega. apply Int.unsigned_range. 
     + apply valid_pointer_null. }
  { simpl in *. clear H.
    forward. forward. forward. entailer!. simpl. rewrite ctxszH3; trivial. }
  { subst; contradiction. } 
  thaw FR1. 
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _tmp_buf md'; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md';
         field_at osh (Tstruct _env_md_ctx_st noattr) []
                    (Vptr b i, (md', (Vundef, Vundef))) octx;
         data_at dsh (Tstruct _env_md_st noattr) (type,
           (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) (Vptr b i);
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (Vptr b i, (md, (nullval, pv2))) ictx)).
  2: solve [inv H].
  { clear H Pd. unfold POSTCONDITION, abbreviate; clear POSTCONDITION. thaw MD'.
    forward_if ( 
      PROP ( )
      LOCAL (gvar ___stringlit_1 ep; temp _tmp_buf md'; temp _out octx; temp _in ictx)
      SEP (ERR ep; memory_block Tsh (Int.unsigned ctxsz) md';
           field_at osh (Tstruct _env_md_ctx_st noattr) []
                    (Vptr b i, (md', (Vundef, Vundef))) octx;
           data_at dsh (Tstruct _env_md_st noattr) (type,
               (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) (Vptr b i);
           data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
           data_at ish (Tstruct _env_md_ctx_st noattr) (Vptr b i, (md, (nullval, pv2))) ictx)).
    { clear H.
      apply denote_tc_test_eq_split; [ | apply valid_pointer_null].
      apply sepcon_valid_pointer1.
      apply sepcon_valid_pointer1.
      apply sepcon_valid_pointer1.
       apply sepcon_valid_pointer2. apply memory_block_valid_ptr. intuition. omega. }
    { clear H. forward. entailer!. cancel. }
    { subst; contradiction. }
    forward. forward. forward. forward.
    (*memcpy*)
    forward_call ((imdsh,Tsh),md', md,Int.unsigned ctxsz, idata).
         { rewrite Int.repr_unsigned; entailer!. }
         { simpl. cancel. }
         { simpl; split; trivial. split; trivial. apply Int.unsigned_range_2. }
    entailer!. }
  forward. forward. forward. 
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _t'5 nullval; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md';
         field_at osh (Tstruct _env_md_ctx_st noattr) []
          (Vptr b i, (md', (Vundef,
             force_val
              (sem_cast (tptr (Tstruct _evp_md_pctx_ops noattr))
               (tptr (Tstruct _evp_md_pctx_ops noattr)) pv2)))) octx;
         data_at dsh (Tstruct _env_md_st noattr)
           (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) (Vptr b i);
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (Vptr b i, (md, (nullval, pv2))) ictx)).
     { contradiction. }
     { forward; entailer!. } 
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md';
         field_at osh (Tstruct _env_md_ctx_st noattr) []
           (Vptr b i, (md', (Vundef,
              force_val
               (sem_cast (tptr (Tstruct _evp_md_pctx_ops noattr))
                (tptr (Tstruct _evp_md_pctx_ops noattr)) pv2)))) octx;
         data_at dsh (Tstruct _env_md_st noattr)
           (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) (Vptr b i);
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (Vptr b i, (md, (nullval, pv2))) ictx)). 
     {  elim H; trivial. }
     { forward; entailer!. }
  forward. unfold POST5. Exists (Vint Int.one); entailer!.

+ (*Case 6: outDigest_Null*)
  rename H into ISH. rename H0 into DSH. rename H1 into OSH. rename H2 into IMDSH.
  rename H3 into cxtszH1. rename H4 into ctxszH2. clear PNd PNmd.
  assert (ctxszH3: Int.eq ctxsz Int.zero=false).
  { remember (Int.eq ctxsz Int.zero) as q. destruct q; trivial.
    apply binop_lemmas2.int_eq_true in Heqq; subst. rewrite Int.unsigned_zero in *. omega. }
  freeze [2;3] FR1.
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _t'1 (Vint Int.zero); temp _tmp_buf (Vint (Int.repr 0));
           temp _out octx; temp _in ictx)
    SEP (ERR ep; FRZL FR1;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)).  
  { subst; contradiction. }
  { clear H. forward. destruct d; try contradiction. forward. entailer!. }

  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _tmp_buf (Vint (Int.repr 0));
           temp _out octx; temp _in ictx)
    SEP (ERR ep; FRZL FR1;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)).
  { elim H; trivial. }
  { clear H. forward. entailer!. }

  thaw FR1. forward. forward. freeze [0;1;2;3] FR1.
  forward_if (
     PROP ( )
     LOCAL (gvar ___stringlit_1 ep; temp _tmp_buf (Vint (Int.repr 0)); temp _out octx; temp _in ictx)
     SEP (FRZL FR1; 
          data_at dsh (Tstruct _env_md_st noattr) vals d)).
  { destruct d; try contradiction; inv H. }
  { clear H. forward. entailer!. }
   
  (*Line 133: cleanup*)
  thaw FR1. focus_SEP 1.
  assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] octx) as FCout by entailer!.
  forward_call (octx, osh, md', pv1', 
         @inl unit (share * val * (reptype (Tstruct _env_md_st noattr))) tt).
  { rewrite ! sepcon_assoc. apply sepcon_derives; [ unfold EVP_MD_CTX_NNnode; entailer! | cancel]. }

  (*line 136: read in->md_data && in->digest->ctx_size*)
  forward.
  replace_SEP 0 (data_at_ osh (Tstruct _env_md_ctx_st noattr) octx).
  { (*holds because of FCout*) rewrite 2 data_at__memory_block. entailer!. }
  forward. simpl. replace (force_val (sem_cast_neutral d)) with d by (destruct d; try contradiction; trivial).

  forward. 
  destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
  simpl in type, mds, flags,ini, upd, fin, ctxsize, blsize.
  deadvars!. simpl in *.
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _t'3 (Vint Int.one); temp _tmp_buf (Vint (Int.repr 0)); 
          temp _out octx; temp _in ictx)
    SEP (ERR ep;
        field_at osh (Tstruct _env_md_ctx_st noattr) [] (d, (Vundef, (Vundef, Vundef))) octx;
        data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
        data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
        data_at dsh (Tstruct _env_md_st noattr) (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) d)).
  { clear H. 
    apply denote_tc_test_eq_split; [ | apply valid_pointer_null]. 
    apply sepcon_valid_pointer1.
    apply sepcon_valid_pointer1.
    apply sepcon_valid_pointer2. apply data_at_valid_ptr. intuition.
       simpl. rewrite Z.mul_1_l, Z.max_r; trivial. omega. apply Int.unsigned_range. }
  { clear H.  
    forward. forward. forward. 
    entailer!. simpl. rewrite ctxszH3; trivial. }
  { subst; contradiction. } 
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _tmp_buf nullval; temp _out octx; temp _in ictx)
    SEP (EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) && 
                 (data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m *
                  field_at osh (Tstruct _env_md_ctx_st noattr) [] (d, (m, (Vundef, Vundef))) octx);
         ERR ep; 
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr)
           (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) d)).
  2: solve [inv H].
  { clear H. 
    forward_if (
      PROP ( )
      LOCAL (gvar ___stringlit_1 ep; temp _tmp_buf nullval; temp _out octx; temp _in ictx)
      SEP (EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) && 
                   (memory_block Tsh (Int.unsigned ctxsz)  m *
                    field_at osh (Tstruct _env_md_ctx_st noattr) [] (d, (m, (Vundef, Vundef))) octx);
           ERR ep; 
           data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
           data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
           data_at dsh (Tstruct _env_md_st noattr)
             (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) d)).
    { contradiction. }
    { clear H. forward. forward.
      forward_call (Int.unsigned ctxsz).
      + rewrite Int.repr_unsigned; entailer!.
      + Intros m. forward. forward. freeze [2;3;4;5] FR1.
        focus_SEP 1.
        apply semax_orp_SEPx; Intros.
        - subst; simpl.
          forward_if (PROP (False) LOCAL () SEP ()); [ | inv H | ].
          * clear H. thaw FR1.
            forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                ep, Vint (Int.repr 142)).
            forward. Exists nullval. entailer!.
            apply orp_right1. entailer!.  
          * intros. old_go_lower. clear H. unfold overridePost; simpl; entailer!. if_tac; entailer!. 
        - rename H into M. 
          rewrite memory_block_isptr; Intros.
          forward_if (
            PROP ( )
            LOCAL (gvar ___stringlit_1 ep; temp _tmp_buf (Vint (Int.repr 0)); 
                   temp _out octx; temp _in ictx)
            SEP (ERR ep; memory_block Tsh (Int.unsigned ctxsz) m; FRZL FR1)).
          * clear H.
            apply denote_tc_test_eq_split; [ | apply valid_pointer_null]. 
            apply sepcon_valid_pointer1.
            apply sepcon_valid_pointer1.
            apply memory_block_valid_ptr; intuition; omega. 
          * destruct m; try contradiction; inv H.
          * clear H. forward. entailer!. 
          * unfold POSTCONDITION, abbreviate, overridePost; intros.
            destruct (EqDec_exitkind ek EK_normal). 
            ++ subst; old_go_lower. entailer!. thaw FR1. Exists m; entailer!. cancel.
            ++ old_go_lower. clear H. rewrite ! if_false; trivial. }
    Intros m. rename H into M. forward. forward. forward. forward.
    (*memcpy*)
    forward_call ((imdsh,Tsh),m, md,Int.unsigned ctxsz, idata).
         { rewrite Int.repr_unsigned; entailer!. }
         { simpl. cancel. }
         { simpl; split; trivial. split; trivial. apply Int.unsigned_range_2. }
    entailer!. Exists m. entailer!. }
  Intros m. rename H into M. forward. forward. forward. 
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _t'5 nullval; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m;
         field_at osh (Tstruct _env_md_ctx_st noattr) []
          (d, (m, (Vundef,
             force_val
              (sem_cast (tptr (Tstruct _evp_md_pctx_ops noattr))
               (tptr (Tstruct _evp_md_pctx_ops noattr)) pv2)))) octx;
         data_at dsh (Tstruct _env_md_st noattr)
           (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d;
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx)).
     { contradiction. }
     { forward; entailer!. } 
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m;
         field_at osh (Tstruct _env_md_ctx_st noattr) []
           (d, (m, (Vundef,
             force_val
              (sem_cast (tptr (Tstruct _evp_md_pctx_ops noattr))
               (tptr (Tstruct _evp_md_pctx_ops noattr)) pv2)))) octx;
         data_at dsh (Tstruct _env_md_st noattr)
           (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d;
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx)). 
     { elim H; trivial. }
     { forward; entailer!. }
  forward. Exists (Vint Int.one); entailer!. unfold POST6. normalize.
  apply orp_right2; Exists m. entailer!.

+ (*Case 7: distinctDigests*)
  rename H into ISH. rename H0 into DSH. rename H1 into OSH. rename H2 into IMDSH.
  rename H3 into cxtszH1. rename H4 into ctxszH2. 
  rename H5 into Hdd'. rename H6 into cxtszH1'. rename H7 into ctxszH2'. clear PNd PNmd PNd'.
  rewrite EVP_MD_NNnode_isptr'; Intros.
  assert (ctxszH3: Int.eq ctxsz Int.zero=false).
  { remember (Int.eq ctxsz Int.zero) as q. destruct q; trivial.
    apply binop_lemmas2.int_eq_true in Heqq; subst. rewrite Int.unsigned_zero in *. omega. }
  freeze [2;5] D'MD'. freeze [0;3;4] FR1.
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _t'1 (Vint Int.zero);
           temp _tmp_buf (Vint (Int.repr 0)); temp _out octx; temp _in ictx)
    SEP (ERR ep; FRZL FR1;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)).  
  { subst; contradiction. }
  { clear H. forward. destruct d; try contradiction. forward. entailer!. }

  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _tmp_buf (Vint (Int.repr 0));
           temp _out octx; temp _in ictx)
    SEP (ERR ep; FRZL FR1;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)).
  { elim H; trivial. }
  { clear H. forward. entailer!. }

  thaw FR1. forward. forward. freeze [0;2;3;4] FR1.
  forward_if (
     PROP ( )
     LOCAL (gvar ___stringlit_1 ep; temp _tmp_buf (Vint (Int.repr 0)); temp _out octx; temp _in ictx)
     SEP (FRZL FR1; FRZL D'MD';
          data_at dsh (Tstruct _env_md_st noattr) vals d)).
  { clear H.
    apply denote_tc_test_eq_split; [ apply sepcon_valid_pointer1 | apply sepcon_valid_pointer2; entailer! ].
    apply sepcon_valid_pointer2. clear. thaw D'MD'.
    apply sepcon_valid_pointer1; unfold EVP_MD_NNnode. clear; entailer!. }
  { destruct d; destruct d'; try contradiction; unfold typed_true, sem_cmp_pp, Val.of_bool in H; simpl in H.
    rewrite if_false in H; simpl in H; try solve [inv H]. 
    intros N; subst; rewrite if_true in H; trivial; simpl in H.
    rewrite Int.eq_false in H; try solve [inv H]. }
  { clear H. forward. entailer!. }
   
  (*Line 133: cleanup*)
  thaw FR1. thaw D'MD'. freeze [0;2;3;6] FR1. 
  assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] octx) as FCout by entailer!.
  forward_call (octx, osh, md', pv1', 
         @inr unit (share * val * (reptype (Tstruct _env_md_st noattr))) (dsh', d', vals')).
  { Exists ctxsz'; unfold EVP_MD_CTX_NNnode. entailer!. } 
  thaw FR1.
  (*line 136: read in->md_data && in->digest->ctx_size*)
  forward.
  replace_SEP 0 (data_at_ osh (Tstruct _env_md_ctx_st noattr) octx).
  { (*holds because of FCout*) rewrite 2 data_at__memory_block. entailer!. }
  forward. simpl. replace (force_val (sem_cast_neutral d)) with d by (destruct d; try contradiction; trivial).

  forward. 
  destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
  simpl in type, mds, flags,ini, upd, fin, ctxsize, blsize.
  deadvars!. simpl in *.
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _t'3 (Vint Int.one); temp _tmp_buf (Vint (Int.repr 0)); 
           temp _out octx; temp _in ictx)
    SEP (ERR ep;
         field_at osh (Tstruct _env_md_ctx_st noattr) [] (d, (Vundef, (Vundef, Vundef))) octx;
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md; EVP_MD_NNnode dsh' vals' d';
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr) (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) d)).
  { clear H. 
    apply denote_tc_test_eq_split; [ | apply valid_pointer_null]. 
    apply sepcon_valid_pointer1.
    apply sepcon_valid_pointer1.
    apply sepcon_valid_pointer2. apply data_at_valid_ptr. intuition.
       simpl. rewrite Z.mul_1_l, Z.max_r; trivial. omega. apply Int.unsigned_range. }
  { clear H.  
    forward. forward. forward. 
    entailer!. simpl. rewrite ctxszH3; trivial. }
  { subst; contradiction. } 
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _tmp_buf nullval; temp _out octx; temp _in ictx)
    SEP (EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) && 
                 (data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m *
                  field_at osh (Tstruct _env_md_ctx_st noattr) [] (d, (m, (Vundef, Vundef))) octx);
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         ERR ep; EVP_MD_NNnode dsh' vals' d';
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
         data_at dsh (Tstruct _env_md_st noattr)
           (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) d)).
  2: solve [inv H].
  { clear H. 
    forward_if (
      PROP ( )
      LOCAL (gvar ___stringlit_1 ep; temp _tmp_buf nullval; temp _out octx; temp _in ictx)
      SEP (EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) && 
                   (memory_block Tsh (Int.unsigned ctxsz)  m *
                    field_at osh (Tstruct _env_md_ctx_st noattr) [] (d, (m, (Vundef, Vundef))) octx);
           data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
           ERR ep; EVP_MD_NNnode dsh' vals' d';
           data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx;
           data_at dsh (Tstruct _env_md_st noattr)
             (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) d)).
    { contradiction. }
    { clear H. forward. forward.
      forward_call (Int.unsigned ctxsz).
      + rewrite Int.repr_unsigned; entailer!.
      + Intros m. forward. forward. freeze [2;3;4;5;6] FR1.
        focus_SEP 1.
        apply semax_orp_SEPx; Intros.
        - subst; simpl.
          forward_if (PROP (False) LOCAL () SEP ()); [ | inv H | ].
          * clear H.
            forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                ep, Vint (Int.repr 142)).
            forward. Exists nullval. entailer!.
            apply orp_right1; thaw FR1; entailer!.
          * intros. old_go_lower. clear H. unfold overridePost; simpl; entailer!. if_tac; entailer!. 
        - rename H into M. 
          rewrite memory_block_isptr; Intros.
          forward_if (
            PROP ( )
            LOCAL (gvar ___stringlit_1 ep; temp _tmp_buf (Vint (Int.repr 0)); 
                   temp _out octx; temp _in ictx)
            SEP (ERR ep; memory_block Tsh (Int.unsigned ctxsz) m; FRZL FR1)).
          * clear H.
            apply denote_tc_test_eq_split; [ | apply valid_pointer_null]. 
            apply sepcon_valid_pointer1. 
            apply sepcon_valid_pointer1.
            apply memory_block_valid_ptr; intuition; omega. 
          * destruct m; try contradiction; inv H.
          * clear H. forward. entailer!.
          * unfold POSTCONDITION, abbreviate, overridePost; intros.
            destruct (EqDec_exitkind ek EK_normal). 
            ++ subst; old_go_lower. entailer!. thaw FR1. Exists m; entailer!. cancel.
            ++ old_go_lower. clear H. rewrite ! if_false; trivial. }
    Intros m. rename H into M. forward. forward. forward. forward.
    (*memcpy*)
    forward_call ((imdsh,Tsh),m, md,Int.unsigned ctxsz, idata).
         { rewrite Int.repr_unsigned; entailer!. }
         { simpl. cancel. }
         { simpl; split; trivial. split; trivial. apply Int.unsigned_range_2. }
    entailer!. Exists m. entailer!. }
  Intros m. rename H into M. forward. forward. forward. 
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _t'5 nullval; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m;
         field_at osh (Tstruct _env_md_ctx_st noattr) []
          (d, (m, (Vundef,
             force_val
              (sem_cast (tptr (Tstruct _evp_md_pctx_ops noattr))
               (tptr (Tstruct _evp_md_pctx_ops noattr)) pv2)))) octx;
         EVP_MD_NNnode dsh' vals' d';
         data_at dsh (Tstruct _env_md_st noattr) (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d;
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx)).
     { contradiction. }
     { forward; entailer!. } 
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m;
         field_at osh (Tstruct _env_md_ctx_st noattr) []
          (d, (m, (Vundef,
             force_val
              (sem_cast (tptr (Tstruct _evp_md_pctx_ops noattr))
               (tptr (Tstruct _evp_md_pctx_ops noattr)) pv2)))) octx;
         EVP_MD_NNnode dsh' vals' d';
         data_at dsh (Tstruct _env_md_st noattr) (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d;
         data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md;
         data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx)). 
     {  elim H; trivial. }
     { forward; entailer!. }
  forward. Exists (Vint Int.one); entailer!. unfold POST7. normalize.
  apply orp_right2; Exists m. entailer!.
Time Qed. 

(*| equalDigests_outDataNull: forall (ish:share) (d md pv1 pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (pv1': val)
                      (imdsh:share) (idata:list int) (ctxsz: int), copyEx_cases
| equalDigests_outDataPtr: forall (ish:share) (d md pv1 pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (pv1': val)
                      (imdsh:share) (idata:list int) (ctxsz: int)
                      (md':val), copyEx_cases
| outDigest_Null: forall (ish:share) (d md pv1 pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (md' pv1': val)
                      (imdsh:share) (idata:list int) (ctxsz: int), copyEx_cases
| cp_distinctDigests: forall (ish:share) (d md pv1 pv2:val) (dsh:share) 
                      (vals : reptype (Tstruct _env_md_st noattr))
                      (osh:share) (d' md' pv1': val)
                      (imdsh:share) (idata:list int) (ctxsz: int)
                      (dsh':share) (vals' : reptype (Tstruct _env_md_st noattr))(ctxsz': int), copy_cases*).

Definition copyPost (c: copy_cases) (ictx octx:val) rv : mpred := 
match c with
   ictxNull => emp
| inDigestNull ish md pv1 pv2 => data_at ish (Tstruct _env_md_ctx_st noattr) (nullval, (md, (pv1, pv2))) ictx
| inDataNull ish d pv1 pv2 dsh vals osh d' md' pv1' => POST3 ictx octx ish d  pv2 (*dsh*) vals osh d' rv

| outDigest_Null ish d md pv1 pv2 dsh vals osh md' pv1' imdsh idata ctxsz  =>
    POST6 ictx octx rv ish d md pv1 pv2 dsh vals osh md' pv1' imdsh idata ctxsz
| distinctDigests ish d md pv1 pv2 dsh vals osh d' md' pv1' imdsh idata ctxsz dsh' vals' ctxsz' =>
    POST7 ictx octx rv ish d md pv1 pv2 dsh vals osh d' md' pv1' imdsh idata ctxsz dsh' vals' ctxsz'
end.

Definition EVP_MD_CTX_copy_ex_SPEC := DECLARE _EVP_MD_CTX_copy_ex
  WITH ep: val, octx:val, ictx:val, case:copyEx_cases
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP ()
      LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
      SEP (ERR ep; copyExPre case ictx octx)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERR ep; copyExPost case ictx octx rv).

(*base on case sictxNull, outDigest_Null

  ictxNull => !!(ictx=nullval)&&emp
| inDigestNull ish md pv1 pv2 => !!(isptr ictx /\ readable_share ish)
                            && EVP_MD_CTX_NNnode ish (nullval, (md, (pv1, pv2))) ictx

Definition copyPre outDigest_Null ish d md pv1 pv2 dsh vals osh md' pv1' imdsh idata ctxsz =>
       !!(isptr ictx /\ isptr octx /\ readable_share ish /\ isptr d /\ 
          readable_share dsh /\ writable_share osh /\ isptr md /\ readable_share imdsh /\
          pv1=nullval /\ is_pointer_or_null pv2 /\
          get_ctxsize vals = Vint ctxsz /\ 4 <= Int.unsigned ctxsz <= Int.max_unsigned)
       && EVP_MD_CTX_NNnode ish (d, (md, (pv1, pv2))) ictx *
          data_at dsh (Tstruct _env_md_st noattr) vals d * 
          EVP_MD_CTX_NNnode osh (nullval, (md', (pv1', nullval))) octx *
          data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md

Definition EVP_MD_CTX_copy_SPEC := DECLARE _EVP_MD_CTX_copy
  WITH ep: val, octx:val, ictx:val, case:copyEx_cases
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP ()
      LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
      SEP (ERR ep; copyPre ictx octx)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERR ep; copyExPost case ictx octx rv).


| outDigest_Null ish d md pv1 pv2 dsh vals osh md' pv1' imdsh idata ctxsz =>
       !!(isptr ictx /\ isptr octx /\ readable_share ish /\ isptr d /\ 
          readable_share dsh /\ writable_share osh /\ isptr md /\ readable_share imdsh /\
          pv1=nullval /\ is_pointer_or_null pv2 /\
          get_ctxsize vals = Vint ctxsz /\ 4 <= Int.unsigned ctxsz <= Int.max_unsigned)
       && EVP_MD_CTX_NNnode ish (d, (md, (pv1, pv2))) ictx *
          data_at dsh (Tstruct _env_md_st noattr) vals d * 
          EVP_MD_CTX_NNnode osh (nullval, (md', (pv1', nullval))) octx *
          data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md
(*
Admitted. (*ONLY put_error - admits remain*)
Unshelve.
(!!(rv=Vint Int.zero) 
 && (field_at osh (Tstruct _env_md_ctx_st noattr) []
       (Vptr b i, nullval, (Vundef, Vundef))) octx *
     data_at idsh (Tstruct _env_md_st noattr) vals d *
     data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
     data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (pv1, pv2))) ictx)

!!(rv=Vint Int.one) 
&& (EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) &&
    data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) m *
    field_at osh (Tstruct _env_md_ctx_st noattr) [] (d, (m, (Vundef, pv2))) octx *
    data_at idsh (Tstruct _env_md_st noattr) vals d *
    data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint idata) md *
    data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ictx)


         deadvars!.
         { entailer!. admit. (*is_pointer_or_null pv1*) } 
aapply data
         forward_call (). normalize. thaw FR1; entailer!.  entailer!. _valid_pointer1.
       apply sepcon_valid_pointer2. apply data_at_valid_ptr. intuition.
       simpl. rewrite Z.mul_1_l, Z.max_r; trivial. admit. (*ok*) apply Int.unsigned_range. 
     + apply valid_pointer_null. rewrite memory_block_isptr. forward.
         PROP (isptr m /\ malloc_compatible (Int.unsigned ctxsz) m)
   LOCAL (temp _t'2 m; temp _t'19 (Vint ctxsz); temp _t'18 (Vptr b i);
   temp _t'3 (Vint Int.one); temp _t'20 md; 
   temp _tmp_buf nullval; temp _out octx; temp _in ictx)
   SEP (ERR ep; memory_block Tsh (Int.unsigned ctxsz) m;
   field_at osh (Tstruct _env_md_ctx_st noattr) []
     (Vptr b i,
     (force_val (sem_cast (tptr tvoid) (tptr tvoid) m),
     (Vundef, Vundef))) octx;
   data_at idsh (Tstruct _env_md_st noattr)
     (type,
     (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz)))))))
     (Vptr b i);
   data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) idata md;
   data_at ish (Tstruct _env_md_ctx_st noattr)
     (Vptr b i, (md, (pv1, pv2))) ictx)).
      { clear H.
        apply denote_tc_test_eq_split; try apply valid_pointer_null.
        apply sepcon_valid_pointer1.
        apply sepcon_valid_pointer1.
        apply sepcon_valid_pointer1.
        apply sepcon_valid_pointer1.
        apply orp_left; normalize. apply valid_pointer_null.
        apply memory_block_valid_ptr. intuition. admit. (*OK*) }
      { forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.repr 100),
                  nullval, Vint (Int.repr 121)). admit. admit. }
  { inv H. } 
       apply sepcon_valid_pointer2. apply data_at_valid_ptr. intuition.
       simpl. rewrite Z.mul_1_l, Z.max_r; trivial. admit. (*ok*) apply Int.unsigned_range. 
     + apply valid_pointer_null. }
          

. forward. 
   EVP_MD_node
     (type,
     (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz)))))))
     (Vptr b i);
   data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) idata md;
   data_at ish (Tstruct _env_md_ctx_st noattr)
     (Vptr b i, (md, (pv1, pv2))) ictx))). 
  (PROP ( )
   LOCAL (temp _t'3 (Vint Int.one); temp _tmp_buf nullval;
          temp _out octx; temp _in ictx)
   SEP (ERR ep; field_at osh (Tstruct _env_md_ctx_st noattr) []
          (Vptr b i, (m, (Vundef, Vundef))) octx;
   EVP_MD_node
     (type,
     (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz)))))))
     (Vptr b i);
   data_at imdsh (tarray tuchar (Int.unsigned ctxsz)) idata md;
   data_at ish (Tstruct _env_md_ctx_st noattr)
     (Vptr b i, (md, (pv1, pv2))) ictx))).
   { 

 Int.eq_true.
     forward. valid_ptr_null. entailer!.
       - thaw FR1. Intros dsh' vals' ctxsz'.
         apply sepcon_valid_pointer1. 
         apply sepcon_valid_pointer1. 
         apply sepcon_valid_pointer1. 
         apply sepcon_valid_pointer1. clear -H. entailer!.
     + apply sepcon_valid_pointer1. emp _t'20 md; temp _t'23 d;
   temp _tmp_buf (if Val.eq d d' then md' else Vint (Int.repr 0));
   temp _out octx; temp _in ictx)
   SEP (ERR ep; FRZL FR1; EVP_MD_node (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) d;
   field_at osh (Tstruct _env_md_ctx_st noattr) []
     (d, (Vundef, (Vundef, Vundef))) octx;
   data_at ish (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, pv2))) ictx)).
  { inv H. }
  { clear H. forward. entailer!. }
  deadvars!.
       Exists ctxsz; entailer. cancel.
  forward_call (octx, osh, md', pv1', 
         @inr unit (prod val (reptype (Tstruct _env_md_st noattr))) (d', vals')).
       { Exists ctxsz'.
         assert (FR: Frame = [FRZL FR2]) (*data_at dsh (Tstruct _env_md_st noattr) vals d; 
                   data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (pv1, pv2))) ictx])*); subst Frame. reflexivity.
         clear FR. simpl. unfold EVP_MD_NNnode. Exists dsh'.
         normalize. apply andp_right; [ apply prop_right; trivial | cancel]. }
       unfold EVP_MD_node, EVP_MD_NNnode. entailer!.
       rewrite distrib_orp_sepcon.
       apply orp_left; thaw FR2; normalize.
       Exists sh vals' ctxsz'. normalize. cancel.
       apply orp_right2. Exists dsh. entailer!. }
  
   assert (exists auxvals:reptype (Tstruct _env_md_ctx_st noattr), auxvals=(d, (nullval, (nullval, pv2)))).
   { eexists; reflexivity. }
   destruct H as [auxvals AUXVALS].
   eapply semax_seq with (Q:=
  (PROP ( )
   LOCAL (temp _tmp_buf (if Val.eq d d' then md' else Vint (Int.repr 0)); 
          temp _out octx; temp _in ictx)
   SEP (ERR ep; EVP_MD_node vals d; data_at_ osh (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr)))
          octx; 
   if Val.eq d d'
   then
    EX ctxsz : int,
    !! (get_ctxsize vals = Vint ctxsz /\
        Int.eq ctxsz Int.zero = false) && emp
   else
    EX dsh' : share,
    (EX vals' : reptype (Tstruct _env_md_st noattr),
     (EX ctxsz' : int,
      !! (readable_share dsh' /\
          get_ctxsize vals' = Vint ctxsz' /\
          Int.eq ctxsz' Int.zero = false) &&
      data_at dsh' (Tstruct _env_md_st noattr) vals' d'));
        data_at ish (Tstruct _env_md_ctx_st noattr) auxvals ictx))).
   { destruct (Val.eq d d'); subst.
     - Intros ctxsz. rename H into ctxszH1. rename H0 into ctxszH2. 
       forward_call (octx, osh, nullval, pv1', 
         @inr unit (prod val (reptype (Tstruct _env_md_st noattr))) (d', vals)).
       { Exists ctxsz. 
         assert (FR: Frame = [data_at ish (Tstruct _env_md_ctx_st noattr) (d', (nullval, (nullval, pv2))) ictx]); subst Frame. reflexivity.
         clear FR. simpl. unfold EVP_MD_NNnode. Exists dsh. entailer!. apply orp_right1; trivial. }
       Exists ctxsz; entailer. cancel.
     - Intros dsh' vals' ctxsz'.
       rename H into DSH'. rename H0 into ctxszH1'. rename H1 into ctxszH2'. 
       rewrite data_at_isptr with (p:=d'). Intros. 
       freeze [0;1] FR2.
       forward_call (octx, osh, md', pv1', 
         @inr unit (prod val (reptype (Tstruct _env_md_st noattr))) (d', vals')).
       { Exists ctxsz'.
         assert (FR: Frame = [FRZL FR2]) (*data_at dsh (Tstruct _env_md_st noattr) vals d; 
                   data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (pv1, pv2))) ictx])*); subst Frame. reflexivity.
         clear FR. simpl. unfold EVP_MD_NNnode. Exists dsh'.
         normalize. apply andp_right; [ apply prop_right; trivial | cancel]. }
       unfold EVP_MD_node, EVP_MD_NNnode. entailer!.
       rewrite distrib_orp_sepcon.
       apply orp_left; thaw FR2; normalize.
       Exists sh vals' ctxsz'. normalize. cancel.
       apply orp_right2. Exists dsh. entailer!. }

  unfold MORE_COMMANDS, abbreviate; subst auxvals. forward.
  replace_SEP 1 (data_at_ osh (Tstruct _env_md_ctx_st noattr) octx).
  { (*holds because of FCout*) rewrite 2 data_at__memory_block. entailer!. }
  forward. simpl. replace (force_val (sem_cast_neutral d)) with d by (destruct d; try contradiction; trivial).

  (*line 136: read in->md_data && in->digest->ctx_size*)
  forward. 
  freeze [2] FR1.
  destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
  simpl in type, mds, flags,ini, upd, fin, ctxsize, blsize. 
  forward_if
  (PROP ( )
   LOCAL (temp _t'3 nullval; temp _t'20 nullval; temp _t'23 d;
   temp _tmp_buf (if Val.eq d d' then md' else Vint (Int.repr 0));
   temp _out octx; temp _in ictx)
   SEP (ERR ep; FRZL FR1; EVP_MD_node (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) d;
   field_at osh (Tstruct _env_md_ctx_st noattr) []
     (d, (Vundef, (Vundef, Vundef))) octx;
   data_at ish (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, pv2))) ictx)).
  { inv H. }
  { clear H. forward. entailer!. }
  deadvars!.
  forward_if 
  (PROP ( )
   LOCAL (temp _tmp_buf (if Val.eq d d' then md' else Vint (Int.repr 0));
   temp _out octx; temp _in ictx)
   SEP (ERR ep; FRZL FR1;
   EVP_MD_node
     (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) d;
   field_at osh (Tstruct _env_md_ctx_st noattr) []
     (d, (Vundef, (Vundef, Vundef))) octx;
   data_at ish (Tstruct _env_md_ctx_st noattr)
     (d, (nullval, (nullval, pv2))) ictx)).
   { elim H; trivial. }
   { clear H. forward; entailer!. }

  forward. 
  freeze [0;1] FR2.
  forward. freeze [0;1] FR3. forward. freeze [0;1] FR4.

  forward_if 
  (PROP ( )
   LOCAL (temp _t'5 nullval; temp _t'12 pv2;
   temp _tmp_buf (if Val.eq d d' then md' else Vint (Int.repr 0));
   temp _out octx; temp _in ictx)  SEP (ERR ep; FRZL FR4)). 
   { inv H. }
   { clear H. forward. entailer!. }

  deadvars!.
  forward_if 
   (PROP ( ) LOCAL (temp _out octx; temp _in ictx) SEP (ERR ep; FRZL FR4)).
  {  elim H; trivial. }
  { clear H. forward. entailer!. }

  forward. Exists Int.one. entailer!. thaw FR4. thaw FR3. thaw FR2. thaw FR1.
  cancel. destruct (Val.eq d d').
  - subst d'; Intros ctxsz; Exists ctxsz; entailer.
  - Intros dsh' vals' ctxs'; Exists dsh' vals' ctxs'; entailer.


 }  normalize.
  (PROP ( )
   LOCAL (temp _t'5 (if Val.eq pv1 nullval then nullval else if Val.eq pv2 nullval then Vint Int.one else Vint Int.zero);
          temp _t'10 pv1; temp _t'12 pv2;
   temp _tmp_buf (if Val.eq d d' then md' else Vint (Int.repr 0));
   temp _out octx; temp _in ictx)
   SEP (ERR ep; FRZL FR1;
   EVP_MD_node
     (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) d;
   field_at osh (Tstruct _env_md_ctx_st noattr) []
     (d,
     (Vundef,
     (Vundef,
     force_val
       (sem_cast (tptr (Tstruct _evp_md_pctx_ops noattr))
          (tptr (Tstruct _evp_md_pctx_ops noattr)) pv2)))) octx;
   data_at ish (Tstruct _env_md_ctx_st noattr)
     (d, (nullval, (pv1, pv2))) ictx)).

  (PROP ( )
   LOCAL (temp _t'3 (if Val.eq md nullval then Vint Int.zero else Vint Int.one);
   temp _t'20 md; temp _t'23 d; temp _t'25 d; 
   temp _t'24 d; temp _tmp_buf md'; temp _out octx; 
   temp _in ictx)
   SEP (ERR ep; field_at osh (Tstruct _env_md_ctx_st noattr) []
          (force_val (sem_cast_neutral d), (Vundef, (Vundef, Vundef))) octx;
        EVP_MD_node vals d;mdDATA (fst idata) ctxsz (map Vint (snd idata)) md;
          data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ictx; FRZL MD')).
  { clear H. 
  forward.

(*OK untile after cleanup*)
Inductive copyEx_cases :=
  ictxNull | indigestNull | indigestPtr.

Definition copyExPre (ictx octx:val) (c: copyEx_cases) : mpred :=
match c with 
  ictxNull => !!(ictx=nullval)&&emp
| indigestNull => !!(isptr ictx) && 
                  (EX ish:_, EX md:_, EX pv1:_, EX pv2:_,
                     !!(readable_share ish)&&
                     EVP_MD_CTX_NNnode ish (nullval, (md, (pv1, pv2))) ictx)
| indigestPtr => !!(isptr ictx) && 
                  (EX ish:_, EX d:_, EX md:_, EX pv1:_, EX pv2:_, EX dsh:_, EX vals:_,
                     (!!(readable_share  ish /\ isptr d /\ readable_share dsh) && EVP_MD_CTX_NNnode ish (d, (md, (pv1, pv2))) ictx *
                         data_at dsh (Tstruct _env_md_st noattr) vals d * 
                         (EX ctxsz:_, mdDATA sh sz data md *
                         (!!(isptr octx) && EX osh:_, EX d':_, EX md':_, EX pv1':_, 
                                             !!(writable_share osh) && EVP_MD_CTX_NNnode osh (d', (md', (pv1', nullval))) octx *
                                             if Val.eq d d' then EX ctxsz:_, !!(get_ctxsize vals = Vint ctxsz /\ Int.eq ctxsz Int.zero=false)&&emp  
                                             else EX dsh':_, EX vals':_, EX ctxsz': _,!!(readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz' /\ Int.eq ctxsz' Int.zero = false) 
                                                        && data_at dsh' (Tstruct _env_md_st noattr) vals' d' *
                                                           ((!!(md' = nullval)&& emp) || memory_block Tsh (Int.unsigned ctxsz') md'))))
end.

(*Note: cases octx==null and d'==null not checked by program*)

Definition copyExPost (ictx octx:val) (c: copyEx_cases) : mpred := emp.
 
Definition EVP_MD_CTX_copy_ex_SPEC := DECLARE _EVP_MD_CTX_copy_ex
  WITH octx:val, ictx:val, case: copyEx_cases
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP ()
      LOCAL (temp _out octx; temp _in ictx)
      SEP (copyExPre ictx octx case)
  POST [ tint] EX i:_,
       PROP ()
       LOCAL (temp ret_temp (Vint i))
       SEP (copyExPost ictx octx case).

Definition Gprog_copy_ex : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [OPENSSL_memcpy_SPEC; OPENSSL_PUT_ERROR_SPEC; OPENSSL_malloc_SPEC; EVP_MD_CTX_cleanup_SPEC4].

Lemma body_EVP_MD_CTX_copy_ex: semax_body Vprog Gprog_copy_ex f_EVP_MD_CTX_copy_ex EVP_MD_CTX_copy_ex_SPEC.
Proof. 
  start_function. forward. destruct case.
+ (*case ictxNull*)
  simpl. normalize.
  forward_if (PROP ( )
   LOCAL (temp _t'1 (Vint Int.one); temp _tmp_buf (Vint (Int.repr 0));
          temp _out octx; temp _in nullval)  
   SEP ()).
  { forward. entailer!. }
  { inv H. }
  forward_if (PROP (False) LOCAL () SEP()).
  { forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.repr 100),
                  nullval, Vint (Int.repr 121)). admit. admit. }
  { inv H. }
  Intros; contradiction.
+ (*case indigestNull*)
  simpl. Intros ish md pv1 pv2. rename H into ISH.
  forward_if 
  (PROP ( )
   LOCAL (temp _t'1 (Vint Int.one); temp _t'26 nullval; temp _tmp_buf (Vint (Int.repr 0)); temp _out octx; 
   temp _in ictx)
   SEP (data_at ish (Tstruct _env_md_ctx_st noattr) (nullval, (md, (pv1, pv2)))
          ictx)).
  { subst; contradiction. }
  { forward. forward. entailer!. }
  deadvars!.  
  forward_if (PROP (False) LOCAL () SEP()).
  { forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.repr 100),
                  nullval, Vint (Int.repr 121)). admit. admit. }
  { inv H. }
  Intros; contradiction.
+ (*indigestPtr *)
  simpl. Intros ish d md pv1 pv2 dsh vals osh d' md' pv1'.
  rename H into ISH. rename H0 into DSH. rename H1 into OSH.
  forward_if 
  (PROP ( )
   LOCAL (temp _t'1 (Vint Int.zero); temp _t'26 d; temp _tmp_buf (Vint (Int.repr 0)); temp _out octx; 
   temp _in ictx)
   SEP (data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (pv1, pv2))) ictx;
        data_at dsh (Tstruct _env_md_st noattr) vals d;
        data_at osh (Tstruct _env_md_ctx_st noattr) (d', (md', (pv1', nullval))) octx;
        if Val.eq d d' then EX ctxsz:_, !!(get_ctxsize vals = Vint ctxsz /\ Int.eq ctxsz Int.zero=false)&&emp  
        else EX dsh':_, EX vals':_, EX ctxsz': _,
              !!(readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz' /\ Int.eq ctxsz' Int.zero = false) 
              && data_at dsh' (Tstruct _env_md_st noattr) vals' d' *
                ((!!(md' = nullval)&& emp) || memory_block Tsh (Int.unsigned ctxsz') md'))).
  { subst; contradiction. }
  { freeze [2;3;4] FR1. forward. forward. thaw FR1. entailer!. destruct d; try contradiction; trivial. }
  deadvars!.
  forward_if
  (PROP ( )
   LOCAL (
   temp _tmp_buf (Vint (Int.repr 0)); temp _out octx;
   temp _in ictx)
   SEP (data_at ish (Tstruct _env_md_ctx_st noattr)
          (d, (md, (pv1, pv2))) ictx;
   data_at dsh (Tstruct _env_md_st noattr) vals d;
   data_at osh (Tstruct _env_md_ctx_st noattr)
     (d', (md', (pv1', nullval))) octx;
   if Val.eq d d' then EX ctxsz:_, !!(get_ctxsize vals = Vint ctxsz /\ Int.eq ctxsz Int.zero=false)&&emp  
        else EX dsh':_, EX vals':_, EX ctxsz': _,
              !!(readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz' /\ Int.eq ctxsz' Int.zero = false) 
              && data_at dsh' (Tstruct _env_md_st noattr) vals' d' *
                 ((!!(md' = nullval)&& emp) || memory_block Tsh (Int.unsigned ctxsz') md'))).
   { elim H; trivial. }
   { clear H. forward. entailer!. }
   freeze [3] FR1. forward. 
   forward.
   forward_if (
   PROP ( )
   LOCAL (temp _tmp_buf (if Val.eq d d' then md' else Vint (Int.repr 0)); temp _out octx;
   temp _in ictx)
   SEP (data_at ish (Tstruct _env_md_ctx_st noattr)
          (d, (md, (pv1, pv2))) ictx;
   data_at dsh (Tstruct _env_md_st noattr) vals d; FRZL FR1;
   data_at osh (Tstruct _env_md_ctx_st noattr)
     (d', (if Val.eq d d' then nullval else md', (pv1', nullval))) octx)).
(*   if Val.eq d d' then EX ctxsz:_, !!(get_ctxsize vals = Vint ctxsz /\ Int.eq ctxsz Int.zero=false)&&emp  
        else EX dsh':_, EX vals':_, EX ctxsz': _,
              !!(readable_share dsh' /\ get_ctxsize vals' = Vint ctxsz' /\ Int.eq ctxsz' Int.zero = false) 
              && data_at dsh' (Tstruct _env_md_st noattr) vals' d')).*)
   { clear H. destruct d; try contradiction.
     apply denote_tc_test_eq_split.
     + destruct (Val.eq (Vptr b i) d'); subst.
       - apply sepcon_valid_pointer1.
         apply sepcon_valid_pointer2. entailer!.
       - thaw FR1. Intros dsh' vals' ctxsz'.
         apply sepcon_valid_pointer1. 
         apply sepcon_valid_pointer1. 
         apply sepcon_valid_pointer1. 
         apply sepcon_valid_pointer1. clear -H. entailer!.
     + apply sepcon_valid_pointer1.
       apply sepcon_valid_pointer2. entailer!. }
   { unfold typed_true, sem_cmp_pp in H. forward.
     destruct (Val.eq d d'); subst; simpl in H.
     + forward. entailer!.
     + destruct d; try contradiction. destruct d'; try contradiction; simpl in H.
       destruct (Int.eq i0 Int.zero); simpl in H; inv H.
       destruct (eq_block b0 b); subst; simpl in H.
       - destruct (Int.eq_dec i0 i); subst; simpl in H. elim n; trivial.
         rewrite Int.eq_false in H; trivial; inv H.
       - inv H. }
   { unfold typed_true, sem_cmp_pp in H. 
     destruct (Val.eq d d'); subst; simpl in H.
     + destruct d'; try contradiction. simpl in H.
       rewrite if_true, Int.eq_true in H; trivial. inv H.
     + forward. entailer!. }
   
   (*Line 133: cleanup*)
   thaw FR1.
   assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] octx) as FCout by entailer!.

   assert (exists auxvals:reptype (Tstruct _env_md_ctx_st noattr), auxvals=(d, (md, (pv1, pv2)))).
   { eexists; reflexivity. }
   destruct H as [auxvals AUXVALS].
   eapply semax_seq with (Q:=
  (PROP ( )
   LOCAL (temp _tmp_buf (if Val.eq d d' then md' else Vint (Int.repr 0)); 
          temp _out octx; temp _in ictx)
   SEP (EVP_MD_node vals d; data_at_ osh (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr)))
          octx; 
   if Val.eq d d'
   then
    EX ctxsz : int,
    !! (get_ctxsize vals = Vint ctxsz /\
        Int.eq ctxsz Int.zero = false) && emp
   else
    EX dsh' : share,
    (EX vals' : reptype (Tstruct _env_md_st noattr),
     (EX ctxsz' : int,
      !! (readable_share dsh' /\
          get_ctxsize vals' = Vint ctxsz' /\
          Int.eq ctxsz' Int.zero = false) &&
      data_at dsh' (Tstruct _env_md_st noattr) vals' d'));
        data_at ish (Tstruct _env_md_ctx_st noattr) auxvals ictx))).
   { destruct (Val.eq d d'); subst.
     - Intros ctxsz. rename H into ctxszH1. rename H0 into ctxszH2. 
       forward_call (octx, osh, nullval, pv1', 
         @inr unit (prod val (reptype (Tstruct _env_md_st noattr))) (d', vals)).
       { Exists ctxsz. assert (FR: Frame = [data_at ish (Tstruct _env_md_ctx_st noattr) (d', (md, (pv1, pv2))) ictx]); subst Frame. reflexivity.
         clear FR. simpl. unfold EVP_MD_NNnode. Exists dsh. entailer!. apply orp_right1; trivial. }
       Exists ctxsz; entailer. cancel.
     - Intros dsh' vals' ctxsz'.
       rename H into DSH'. rename H0 into ctxszH1'. rename H1 into ctxszH2'. 
       rewrite data_at_isptr with (p:=d'). Intros. 
       freeze [0;1] FR2.
       forward_call (octx, osh, md', pv1', 
         @inr unit (prod val (reptype (Tstruct _env_md_st noattr))) (d', vals')).
       { Exists ctxsz'.
         assert (FR: Frame = [FRZL FR2]) (*data_at dsh (Tstruct _env_md_st noattr) vals d; 
                   data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (pv1, pv2))) ictx])*); subst Frame. reflexivity.
         clear FR. simpl. unfold EVP_MD_NNnode. Exists dsh'.
         normalize. apply andp_right; [ apply prop_right; trivial | cancel]. }
       unfold EVP_MD_node, EVP_MD_NNnode. entailer!.
       rewrite distrib_orp_sepcon.
       apply orp_left; thaw FR2; normalize.
       Exists sh vals' ctxsz'. normalize. cancel.
       apply orp_right2. Exists dsh. entailer!. }

  unfold MORE_COMMANDS, abbreviate; subst auxvals. forward.
  replace_SEP 1 (data_at_ osh (Tstruct _env_md_ctx_st noattr) octx).
  { (*holds because of FCout*) rewrite 2 data_at__memory_block. entailer!. }
  forward. simpl. replace (force_val (sem_cast_neutral d)) with d by (destruct d; try contradiction; trivial).

  (*line 136: read in->md_data && in->digest->ctx_size*)
  forward. freeze [2] FR1.
  destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
  simpl in type, mds, flags,ini, upd, fin, ctxsize, blsize. 
  forward_if
  (PROP ( )
   LOCAL (temp _t'3 (if Val.eq md nullval then Vint Int.zero else ctxsize); temp _t'20 md; temp _t'23 d;
   temp _tmp_buf (if Val.eq d d' then md' else Vint (Int.repr 0));
   temp _out octx; temp _in ictx)
   SEP (FRZL FR1; EVP_MD_node (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) d;
   field_at osh (Tstruct _env_md_ctx_st noattr) []
     (d, (Vundef, (Vundef, Vundef))) octx;
   data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (pv1, pv2))) ictx)).
  { clear H.

  (PROP ( )
   LOCAL (temp _t'3 (if Val.eq md nullval then Vint Int.zero else Vint Int.one);
   temp _t'20 md; temp _t'23 d; temp _t'25 d; 
   temp _t'24 d; temp _tmp_buf md'; temp _out octx; 
   temp _in ictx)
   SEP (field_at osh (Tstruct _env_md_ctx_st noattr) []
          (force_val (sem_cast_neutral d), (Vundef, (Vundef, Vundef))) octx;
        EVP_MD_node vals d;mdDATA (fst idata) ctxsz (map Vint (snd idata)) md;
          data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ictx; FRZL MD')).
  { clear H. 
  forward.
continue here by partially copying from below.
  freeze [0;2;3] FR3.
  assert_PROP (isptr octx) by entailer!. 
  destruct octx; try contradiction. unfold data_at_, field_at_. simpl. forward. focus_SEP 1. rewrite data_at__isptr. Intros x. normalize. forward.
 normalize. normalize. entailer. Exists
       Exists dsh' vals' ctxsz'. entailer. cancel.
       rewrite sepcon_comm. apply sepcon_derives; unfold EVP_MD_node.
       apply orp_right2. Exists dsh. entailer!.
       apply orp_left; normalize. unfold EVP_MD_NNnode. Intros dsh''. 


semax Delta
  (PROP ( )
   LOCAL (temp _tmp_buf (if Val.eq d d' then md' else Vint (Int.repr 0); 
          temp _out octx; temp _in ictx)
   SEP (data_at_ osh (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr)))
          octx; EVP_MD_node vals d';
   data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (pv1, pv2))) ictx))

   - Intros dsh' vals' ctxsz'.
     rename H into DSH'. rename H0 into ctxszH1'. rename H1 into ctxszH2'. 
     rewrite data_at_isptr with (p:=d'). Intros.
     forward_call (octx, osh, md', pv1', 
       @inr unit (prod val (reptype (Tstruct _env_md_st noattr))) (d', vals')).
     { Exists ctxsz'.
       assert (FR: Frame = [data_at dsh (Tstruct _env_md_st noattr) vals d; 
                 data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (pv1, pv2))) ictx]); subst Frame. reflexivity.
       clear FR. simpl. unfold EVP_MD_NNnode. Exists dsh'.
       normalize. apply andp_right; [ apply prop_right; trivial | cancel]. }

semax Delta
  (PROP ( )
   LOCAL (temp _tmp_buf (Vint (Int.repr 0)); 
   temp _out octx; temp _in ictx)
   SEP (data_at_ osh
          (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr)))
          octx; EVP_MD_node vals' d';
   data_at dsh (Tstruct _env_md_st noattr) vals d;
   data_at ish (Tstruct _env_md_ctx_st noattr)
     (d, (md, (pv1, pv2))) ictx))

  (Ssequence

     {
      entailer!. cancel. apply orp_right1. entailer!. 

       x cancel. Exists
     
   -
   forward_call (octx, osh, if Val.eq d d' then nullval else md', pv1', 
       @inr unit (prod val (reptype (Tstruct _env_md_st noattr))) (d', if Val.eq d d' then vals else vals')).
 intuition. entailer!. } rewrite data_at_isptr with (p:=d').
       Intros. destruct d; try contradiction. destruct d'; try contradiction. simpl in H.
       destruct (eq_block b0 b); subst; simpl in H.
       - destruct (Int.eq_dec i0 i); subst; simpl in H. elim n; trivial.
         rewrite Int.eq_false in H; trivial; inv H.
       - inv H. }
       elim n. simpl in H.
       forward. entailer!.
     destruct (Val.eq d d'); trivial.
     destruct d; try contradiction.  simpl in H.

       apply sepcon_valid_pointer1.
       apply sepcon_valid_pointer1.
       apply sepcon_valid_pointer2. entailer!.
     + }
    apply data_at_valid_ptr; simpl.x entailer.
    apply sepcon_valid_pointer1. 
    apply sepcon_valid_pointer2. entailer. forward.entailer. }
  deadvars!. 
  forward_if (PROP ( )
   LOCAL (
   temp _tmp_buf (Vint (Int.repr 0)); temp _out octx;
   temp _in ictx)
   SEP (data_at ish (Tstruct _env_md_ctx_st noattr)
          (nullval, (md, (pv1, pv2))) ictx;
   data_at dsh (Tstruct _env_md_st noattr) vals d)).
  { elim H; trivial. }
  { clear H. forward. entailer!. }
  x
  { forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.repr 100),
                  nullval, Vint (Int.repr 121)). admit. admit. }
  { inv H. }
  Intros; contradiction. Unshelve.

simpl. destruct ictx; try contradiction. clear H0. rename H into ISH.
    forward. forward. entailer. clear H.
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply data_at_valid_ptr; simpl. entailer.
    apply sepcon_valid_pointer1. 
    apply sepcon_valid_pointer2. entailer. forward. }
  {  normalize.

 }
  { 
   rename H into ptrN_d'. rename H0 into ptrN_md'.
  rename H1 into H1ctxsize. rename H2 into H2ctxsize. subst pv1 pv2. 
  rename SH into iSH; rename SH0 into oSH; rename SH1 into RiSH.
  freeze [4] MD'.
  freeze [0;1;2;3;4] FR1. forward. thaw FR1. 
  focus_SEP 1. apply semax_orp_SEPx; Intros; subst.
{ (*in==null*)
  forward_if (
   PROP ( )
   LOCAL (temp _t'1 (Vint Int.one); temp _tmp_buf (Vint (Int.repr 0)); 
          temp _out octx; temp _in nullval)
   SEP (EVP_MD_node vals d; mdDATA (fst idata) ctxsz (map Vint (snd idata)) md;
        (*data_at osh (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr))) D octx*)
        data_at osh (Tstruct _env_md_ctx_st noattr) (d', (md', (pv1', nullval))) octx;
        FRZL MD')).
  { freeze [0;1;2;3;4] FR1. forward. thaw FR1. entailer!. }
  { inv H. }
  forward_if  
  (PROP ( False )
   LOCAL ()
   SEP ()).
  { forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.repr 100),
                  nullval, Vint (Int.repr 121)). admit. admit. }
  { inv H. }
  Intros; contradiction. }
unfold EVP_MD_CTX_NNnode. rewrite data_at_isptr; Intros. 
focus_SEP 2.
apply semax_orp_SEPx; Intros; subst.


EVP_MD_CTX_node ish (d, (md, (pv1, pv2))) ictx; 
            mdDATA (fst idata) ctxsz (map Vint (snd idata)) md; EVP_MD_node vals d;
            if Val.eq d nullval
            then (!!(i=Int.zero) && 
                     data_at osh (Tstruct _env_md_ctx_st noattr) (d', (md', (pv1', nullval))) octx *
                     memory_block Tsh (Int.unsigned ctxsz') md')
            else
           (!!(md' = nullval) && EX m:_, EVP_MD_CTX_NNnode osh (d, (m, (Vundef, pv2))) octx *
                                 data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint (snd idata)) m) 
           || (EX ctxsz':int, !!(Int.eq ctxsz' Int.zero=false) 
                                          && memory_block Tsh (Int.unsigned ctxsz') md' *
                                             EVP_MD_CTX_NNnode osh (d, (md', (Vundef, pv2))) octx *
                                          if Val.eq d d' then !!(ctxsz'=ctxsz)&&emp
                                          else EX vals':_, !!(get_ctxsize vals' = Vint ctxsz') &&  EVP_MD_NNnode vals' d')).

(*case md=nullval: md, pv1=Vundef rather than nullval in octx*)
(*case md<>nullval, md'=nullval: exists m, m in octx, pv1=Vundef not nullval, star data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint (snd idata)) m*)
(*case md<>null, md'<>null: md -> md', pv1 Vundef not null*)

Definition Gprog_copy_ex : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [OPENSSL_memcpy_SPEC; OPENSSL_PUT_ERROR_SPEC; OPENSSL_malloc_SPEC; EVP_MD_CTX_cleanup_SPEC4].

Lemma mdDATA1 sh sz d p: data_at sh (tarray tuchar (Int.unsigned sz)) d p |--
                         mdDATA sh sz d p.
Proof. apply orp_right2. entailer!. Qed.

Lemma mdDATA2 sh sz d: mdDATA sh sz d nullval = emp.
Proof. unfold mdDATA. apply pred_ext. entailer!. apply orp_left; trivial. entailer!.
   apply orp_right1. entailer!. Qed.

Lemma EVP_MD_CTX_node1 sh d md pv1 pv2 p: 
  is_pointer_or_null d -> is_pointer_or_null md ->
  data_at sh (Tstruct _env_md_ctx_st noattr) (d, (md, (pv1,pv2))) p
                                  |-- EVP_MD_CTX_node sh (d, (md, (pv1,pv2))) p.
Proof. intros.
    simpl in *.
    apply orp_right2. unfold EVP_MD_CTX_NNnode. entailer!.
Qed.

Hint Resolve mdDATA1: cancel.
Hint Extern 10 (data_at _ (Tstruct _env_md_ctx_st noattr) _ _
                                  |-- EVP_MD_CTX_node _ _ _ ) =>
   apply EVP_MD_CTX_node1 : cancel.

Lemma body_EVP_MD_CTX_copy_ex: semax_body Vprog Gprog_copy_ex f_EVP_MD_CTX_copy_ex EVP_MD_CTX_copy_ex_SPEC.
Proof. 
  start_function. rename H into ptrN_d'. rename H0 into ptrN_md'.
  rename H1 into H1ctxsize. rename H2 into H2ctxsize. subst pv1 pv2. 
  rename SH into iSH; rename SH0 into oSH; rename SH1 into RiSH.
  freeze [4] MD'.
  freeze [0;1;2;3;4] FR1. forward. thaw FR1. 
  focus_SEP 1. apply semax_orp_SEPx; Intros; subst.
{ (*in==null*)
  forward_if (
   PROP ( )
   LOCAL (temp _t'1 (Vint Int.one); temp _tmp_buf (Vint (Int.repr 0)); 
          temp _out octx; temp _in nullval)
   SEP (EVP_MD_node vals d; mdDATA (fst idata) ctxsz (map Vint (snd idata)) md;
        (*data_at osh (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr))) D octx*)
        data_at osh (Tstruct _env_md_ctx_st noattr) (d', (md', (pv1', nullval))) octx;
        FRZL MD')).
  { freeze [0;1;2;3;4] FR1. forward. thaw FR1. entailer!. }
  { inv H. }
  forward_if  
  (PROP ( False )
   LOCAL ()
   SEP ()).
  { forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.repr 100),
                  nullval, Vint (Int.repr 121)). admit. admit. }
  { inv H. }
  Intros; contradiction. }
unfold EVP_MD_CTX_NNnode. rewrite data_at_isptr; Intros. 
focus_SEP 2.
apply semax_orp_SEPx; Intros; subst.
{ (*d==null*)
  destruct ictx; try contradiction. clear Pictx. 
  forward_if (PROP ( )
   LOCAL (temp _t'1 (Vint Int.one); temp _tmp_buf (Vint (Int.repr 0)); temp _out octx;
   temp _in (Vptr b i))
   SEP (data_at ish (Tstruct _env_md_ctx_st noattr) (nullval, (md, (nullval, nullval))) (Vptr b i); 
        FRZL MD'; mdDATA (fst idata) ctxsz (map Vint (snd idata)) md;
        data_at osh (Tstruct _env_md_ctx_st noattr) (d', (md', (pv1', nullval))) octx)).
  + elim H; trivial.
  + freeze [0;2;3;4;5] FR1. forward. forward. thaw FR1. entailer!. 
  + forward_if (PROP (False) LOCAL () SEP()).
    - forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.repr 100),
                  nullval, Vint (Int.repr 121)). admit. admit.
      forward. Exists Int.zero. simpl. unfold nullval. rewrite Valeq_Vint, Int.eq_true.
      entailer!. 
      thaw MD'. cancel. apply orp_left. 
      * apply orp_right1. entailer!.  
      * normalize. destruct (Val.eq nullval d'); subst.  apply orp_right1. entailer!.
    - inv H. } 

(*case isptr d, isptr ictx*)
(*line 120:(in == NULL || in->digest == NULL) is false*)
destruct (Val.eq d d').
+ (*Case 1*)
  subst d'; unfold EVP_MD_NNnode; Intros sh. rename H into Rsh. 
  rewrite data_at_isptr; Intros. clear PNd.
  forward_if (
   PROP ( )
   LOCAL (temp _t'1 (Vint Int.zero); temp _tmp_buf (Vint (Int.repr 0)); 
          temp _out octx; temp _in ictx)
   SEP (data_at sh (Tstruct _env_md_st noattr) vals d;
        mdDATA (fst idata) ctxsz (map Vint (snd idata)) md; FRZL MD';
        data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ictx;
        data_at osh (Tstruct _env_md_ctx_st noattr) (d, (md', (pv1', nullval))) octx)).
  { subst; contradiction. }
  { forward. forward. destruct d; try contradiction. entailer!. }

  forward_if 
  (PROP ( )
   LOCAL (temp _t'1 (Vint Int.zero);
   temp _tmp_buf (Vint (Int.repr 0)); 
   temp _out octx; temp _in ictx)
   SEP (data_at sh (Tstruct _env_md_st noattr) vals d; 
        mdDATA (fst idata) ctxsz (map Vint (snd idata)) md;
   data_at ish (Tstruct _env_md_ctx_st noattr)
     (d, (md, (nullval, nullval))) ictx; FRZL MD';
   data_at osh (Tstruct _env_md_ctx_st noattr)
     (d, (md', (pv1', nullval))) octx)).

  { elim H; trivial. }
  { forward. entailer!. }

  (*line 125: read in->digest and out->digest*)
  forward. forward.
  (*We're in case d=d', so remove mddata from out*) 
  forward_if 
  (PROP ( )
   LOCAL (temp _t'25 d; temp _t'24 d; temp _tmp_buf md';
          temp _out octx; temp _in ictx)
   SEP (data_at sh (Tstruct _env_md_st noattr) vals d;mdDATA (fst idata) ctxsz (map Vint (snd idata)) md;
   data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ictx; FRZL MD';
   data_at osh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (pv1', nullval))) octx)).
  { (*left branch*)
    forward. forward. entailer!. }
  { (*right branch*)
    destruct d; try contradiction.
    unfold typed_false, sem_cmp_pp in H; simpl in H.
    destruct (eq_block b b); try solve [inv H].
    rewrite Int.eq_true in H; inv H. }

  assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] octx) as FCout by entailer!.

  (*Line 133: call cleanup*)
  forward_call (octx, osh, nullval, pv1', 
    @inr unit (prod val (reptype (Tstruct _env_md_st noattr))) (d, vals)).
  { Exists ctxsz. 
    assert (FR: Frame = [data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ictx;
                         mdDATA (fst idata) ctxsz (map Vint (snd idata)) md;
                         FRZL MD']); subst Frame; [ reflexivity | clear FR; simpl].
    entailer!. unfold EVP_MD_NNnode. Exists sh. entailer!. apply orp_right1; trivial. }

  (*Line 135: out->digest = in->digest;*)
  forward.
  replace_SEP 0 (data_at_ osh (Tstruct _env_md_ctx_st noattr) octx).
  { (*holds because of FCout*) rewrite 2 data_at__memory_block. entailer!. }
  forward. simpl.

  (*line 136: read in->md_data && in->digest->ctx_size*)
  forward.
  forward_if
  (PROP ( )
   LOCAL (temp _t'3 (if Val.eq md nullval then Vint Int.zero else Vint Int.one);
   temp _t'20 md; temp _t'23 d; temp _t'25 d; 
   temp _t'24 d; temp _tmp_buf md'; temp _out octx; 
   temp _in ictx)
   SEP (field_at osh (Tstruct _env_md_ctx_st noattr) []
          (force_val (sem_cast_neutral d), (Vundef, (Vundef, Vundef))) octx;
        EVP_MD_node vals d;mdDATA (fst idata) ctxsz (map Vint (snd idata)) md;
          data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ictx; FRZL MD')).
  { clear H. 
    apply denote_tc_test_eq_split; try apply valid_pointer_null. 
    apply sepcon_valid_pointer1. 
    apply sepcon_valid_pointer2.
    apply mdDATA_validptr. trivial. simpl. rewrite Z.mul_1_l, Z.max_r; trivial.
    apply int_eq_false_e in H2ctxsize. admit. (*ok
     elim H2ctxsize. unfold Int.zero. 
    rewrite e, Int.repr_unsigned; trivial.
      destruct (Int.unsigned_range ctxsz). omega.
      apply Int.unsigned_range.*) }
  { forward. focus_SEP 1.
    apply semax_orp_SEPx; Intros; subst. contradiction.
    unfold EVP_MD_NNnode. Intros iish. (*duplication with ish!*)
    destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
    simpl in type, mds, flags,ini, upd, fin, ctxsize, blsize, H1ctxsize; subst.
    forward.
    forward. 
    rewrite if_false. 2: destruct md; try contradiction; discriminate.
    entailer!. simpl. rewrite H2ctxsize; trivial.
    apply orp_right2. Exists iish. entailer!. }
  { subst. forward. entailer!. }
  deadvars!. 

  forward_if (
PROP ( )
LOCAL (temp _tmp_buf md'; temp _out octx; temp _in ictx)
SEP (
if Val.eq md nullval 
then field_at osh (Tstruct _env_md_ctx_st noattr) []
  (force_val (sem_cast_neutral d),
  (Vundef, (Vundef, Vundef))) octx * FRZL MD'
else data_at (fst (fst idata, Tsh))
       (tarray tuchar (Int.unsigned ctxsz))
       (map Vint (snd idata)) md *
     if Val.eq md' nullval 
     then EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) &&
          field_at osh (Tstruct _env_md_ctx_st noattr) [] (d, (m, (Vundef, Vundef))) octx * 
          data_at (snd (fst idata, Tsh)) (tarray tuchar (Int.unsigned ctxsz)) (map Vint (snd idata)) m
     else field_at osh (Tstruct _env_md_ctx_st noattr) [] (d, (md', (Vundef, Vundef))) octx * 
          data_at (snd (fst idata, Tsh)) (tarray tuchar (Int.unsigned ctxsz)) (map Vint (snd idata)) md';
EVP_MD_node vals d;
data_at ish (Tstruct _env_md_ctx_st noattr)
  (d, (md, (nullval, nullval))) ictx)).

  { destruct (Val.eq md nullval); subst; try solve [inv H].
    clear H. 
    freeze [1;2;3] FR2. focus_SEP 2.
    forward_if (
PROP ( )
LOCAL (temp _t'3 (Vint Int.one); temp _tmp_buf md'; 
temp _out octx; temp _in ictx)
SEP (FRZL FR2;
if Val.eq md' nullval 
then EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) && 
memory_block Tsh (Int.unsigned ctxsz) m * FRZL MD' *
field_at osh (Tstruct _env_md_ctx_st noattr) []
  (d, (m, (Vundef, Vundef))) octx

 else ((*EX ctxsz': int,*)
 memory_block Tsh (Int.unsigned ctxsz(*'*)) md' * field_at osh (Tstruct _env_md_ctx_st noattr) []
     (force_val (sem_cast_neutral d), (md', (Vundef, Vundef))) octx))). 
    { clear H. thaw FR2; thaw MD'. destruct md'; try contradiction; simpl in ptrN_md'; subst.
      apply denote_tc_test_eq_split; apply valid_pointer_null. 
      apply denote_tc_test_eq_split; try apply valid_pointer_null. 
      apply sepcon_valid_pointer1.
      apply sepcon_valid_pointer1.
      apply sepcon_valid_pointer1.
      apply orp_left; normalize; [ discriminate |]. 
      apply memory_block_valid_ptr. intuition. admit. (*OK*) }
    { unfold POSTCONDITION, abbreviate; clear POSTCONDITION. thaw FR2; thaw MD'.
      apply semax_orp_SEPx; Intros; subst; try contradiction.
      Intros ctxsz'. subst ctxsz'. forward. rewrite if_false. 2: destruct md'; try contradiction; discriminate.
      (*Exists ctxsz'.*) entailer!. cancel. }
    { subst. (*md'=nullval,  md <> nullval*)
      unfold POSTCONDITION, abbreviate; clear POSTCONDITION. thaw FR2.
      forward. focus_SEP 1. apply semax_orp_SEPx; Intros; subst; try contradiction.
      unfold EVP_MD_NNnode. Intros idsh. destruct d; simpl in Pd; try contradiction.
      freeze [1;2;3;4] FR2.
      destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
      simpl in type, mds, flags,ini, upd, fin, ctxsize, blsize, H1ctxsize; subst.
      forward. 
      forward_call (Int.unsigned ctxsz).
        rewrite Int.repr_unsigned. entailer!. admit. (*new condition: 4 <= Int.unsigned ctxsz <= Int.max_unsigned*)
      Intros m. thaw FR2.
      forward. forward.
      forward_if (
  (PROP (isptr m /\ malloc_compatible (Int.unsigned ctxsz) m)
   LOCAL (
   temp _t'2 m; temp _t'19 (Vint ctxsz); temp _t'18 (Vptr b i);
   temp _t'3 (Vint Int.one); temp _tmp_buf nullval; 
   temp _out octx; temp _in ictx)
   SEP (memory_block Tsh (Int.unsigned ctxsz) m; 
   FRZL MD';
   field_at osh (Tstruct _env_md_ctx_st noattr) []
     (force_val (sem_cast_neutral (Vptr b i)),
     (force_val (sem_cast (tptr tvoid) (tptr tvoid) m),
     (Vundef, Vundef))) octx;
   mdDATA (fst idata) ctxsz (map Vint (snd idata)) md;
   data_at ish (Tstruct _env_md_ctx_st noattr)
     (Vptr b i, (md, (nullval, nullval))) ictx;
   data_at idsh (Tstruct _env_md_st noattr)
     (type,
     (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz)))))))
     (Vptr b i)))).
    { clear H0.
      apply denote_tc_test_eq_split; try apply valid_pointer_null.
      apply sepcon_valid_pointer1. 
      apply sepcon_valid_pointer1.  
      apply sepcon_valid_pointer1. 
      apply sepcon_valid_pointer1.  
      apply sepcon_valid_pointer1. apply orp_left; normalize. apply valid_pointer_null. 
      apply memory_block_valid_ptr. intuition. admit. (*OK*) }
    { unfold typed_true in H0; apply semax_orp_SEPx; Intros; subst; [ clear H0; simpl | rewrite memory_block_isptr; Intros; destruct m; try contradiction; inv H0].
      forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or Int.one (Int.repr 64)),
                  nullval, Vint (Int.repr 142)). admit. admit.
      forward. Exists Int.zero. rewrite Int.eq_true. entailer.
      admit. (*TODO: correct postcondition to deal with failed malloc*) } 
    { unfold typed_true in H0; apply semax_orp_SEPx; Intros; subst; [ inv H0 | clear H0; simpl]. 
      forward. entailer!. }
    intros. unfold POSTCONDITION, abbreviate, overridePost. 
    old_go_lower. clear H0.
    destruct (EqDec_exitkind ek EK_normal); trivial. rewrite if_true; trivial.
    Exists m. entailer. cancel. 
    apply orp_right2. Exists idsh. entailer!. }

  (*line 146: memcpy*)
  destruct (Val.eq md' nullval).
  + Intros m. forward. thaw FR2. forward. forward.
    apply semax_orp_SEPx; Intros; subst; try contradiction.
    unfold EVP_MD_NNnode. Intros idsh. destruct d; simpl in Pd; try contradiction.
    destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
    simpl in type, mds, flags,ini, upd, fin, ctxsize, blsize, H1ctxsize; subst.
    forward. freeze [0;2;4;5] FR2.
    focus_SEP 1. apply semax_orp_SEPx; Intros; subst; try contradiction.
    forward_call ((fst idata,Tsh),m, md,Int.unsigned ctxsz, snd idata).
    { rewrite Int.repr_unsigned; simpl. entailer!. }
    { simpl. cancel. }
    { simpl. split; trivial. split. intuition. apply Int.unsigned_range_2. }
    Exists m. thaw FR2; thaw MD'; entailer!.
    apply orp_right2. Exists idsh. apply andp_right; [apply prop_right; trivial | cancel].
    apply orp_left; trivial. entailer!. rewrite memory_block_isptr. Intros; contradiction.
  + (*Intros ctxsz'.*) thaw FR2. forward. forward. forward.
    apply semax_orp_SEPx; Intros; subst; try contradiction.
    unfold EVP_MD_NNnode. Intros idsh. destruct d; simpl in Pd; try contradiction.
    destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
    simpl in type, mds, flags,ini, upd, fin, ctxsize, blsize, H1ctxsize; subst.
    forward.  freeze [0;2;4;5] FR2.
    focus_SEP 1. apply semax_orp_SEPx; Intros; subst; try contradiction.
    forward_call ((fst idata,Tsh), md', md, Int.unsigned ctxsz(*'*), snd idata).
    { rewrite Int.repr_unsigned; simpl. entailer!. }
    { simpl. cancel. }
    { simpl. split; trivial. split. intuition. apply Int.unsigned_range_2. }
    thaw FR2; entailer!. apply orp_right2. Exists idsh. entailer!. }

  { unfold typed_false in H. destruct (Val.eq md nullval); simpl in H; [clear H; subst | inv H].
    focus_SEP 2. apply semax_orp_SEPx; Intros; subst; try contradiction.
    forward.
    thaw MD'; entailer!. }

  (*line 150:out->pctx_ops = in->pctx_ops;*)
  freeze [0] FR1. forward. thaw FR1.
  destruct (Val.eq md nullval).
  - subst. normalize. forward. forward. 
    forward_if (PROP ( )
   LOCAL (temp _t'5 (Vint Int.zero); temp _t'10 nullval; temp _t'12 nullval;
   temp _tmp_buf md'; temp _out octx; temp _in ictx)
   SEP (field_at osh (Tstruct _env_md_ctx_st noattr) []
          (d, (Vundef, (Vundef, Vint Int.zero))) octx;
   FRZL MD'; EVP_MD_node vals d;
   data_at ish (Tstruct _env_md_ctx_st noattr)
     (d, (nullval, (nullval, nullval))) ictx)).
    { contradiction. }
    { forward. entailer!. }
   forward_if
  (PROP ( )
   LOCAL (temp _t'5 (Vint Int.zero);
   temp _t'10 nullval; temp _t'12 nullval;
   temp _tmp_buf md'; temp _out octx;
   temp _in ictx)
   SEP (field_at osh
          (Tstruct _env_md_ctx_st noattr) []
          (d, (Vundef, (Vundef, Vint Int.zero)))
          octx; FRZL MD'; EVP_MD_node vals d;
   data_at ish (Tstruct _env_md_ctx_st noattr)
     (d, (nullval, (nullval, nullval))) ictx)).
     { elim H; trivial. }
     { forward. entailer!. }
     forward. Exists Int.one. simpl. thaw MD'.
     rewrite mdDATA2. entailer!.
     admit.x (*case md=nullval: md, pv1=Vundef rather than nullval in octx*)
   - destruct (Val.eq md' nullval).
     * subst. Intros m. forward. forward.
       forward_if
  (PROP ( )
   LOCAL (temp _t'5 nullval; temp _t'12 nullval;
   temp _tmp_buf nullval; temp _out octx; temp _in ictx)
   SEP (data_at (fst (fst idata, Tsh))
          (tarray tuchar (Int.unsigned ctxsz)) 
          (map Vint (snd idata)) md;
   field_at osh (Tstruct _env_md_ctx_st noattr) []
     (d, (m, (Vundef, Vint Int.zero))) octx;
   data_at (snd (fst idata, Tsh)) (tarray tuchar (Int.unsigned ctxsz))
     (map Vint (snd idata)) m; EVP_MD_node vals d;
   data_at ish (Tstruct _env_md_ctx_st noattr)
     (d, (md, (nullval, nullval))) ictx)).
       { contradiction. }
       { forward. entailer!. }
   forward_if
  (PROP ( )
   LOCAL (temp _t'12 nullval;
   temp _tmp_buf nullval; temp _out octx; temp _in ictx)
   SEP (data_at (fst (fst idata, Tsh))
          (tarray tuchar (Int.unsigned ctxsz)) 
          (map Vint (snd idata)) md;
   field_at osh (Tstruct _env_md_ctx_st noattr) []
     (d, (m, (Vundef, Vint Int.zero))) octx;
   data_at (snd (fst idata, Tsh)) (tarray tuchar (Int.unsigned ctxsz))
     (map Vint (snd idata)) m; EVP_MD_node vals d;
   data_at ish (Tstruct _env_md_ctx_st noattr)
     (d, (md, (nullval, nullval))) ictx)).
     { elim H0; trivial. }
     { forward. entailer!. }
     forward. Exists Int.one; simpl; entailer!.
     admit. x(*case md<>nullval, md'=nullval: exists m, m in octx, pv1=Vundef not nullval, star data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint (snd idata)) m*)
   * rewrite field_at_isptr. Intros. destruct octx; try contradiction.
     forward. forward. 
   forward_if
  (PROP ( )
   LOCAL (temp _t'5 nullval; temp _t'12 nullval; 
   temp _tmp_buf md'; temp _out (Vptr b i); temp _in ictx)
   SEP (data_at (fst (fst idata, Tsh)) (tarray tuchar (Int.unsigned ctxsz))
          (map Vint (snd idata)) md;
   field_at osh (Tstruct _env_md_ctx_st noattr) []
     (d, (md', (Vundef, Vint Int.zero))) (Vptr b i);
   data_at (snd (fst idata, Tsh)) (tarray tuchar (Int.unsigned ctxsz))
     (map Vint (snd idata)) md'; EVP_MD_node vals d;
   data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval)))
     ictx)).
     { contradiction. }
     { forward. entailer!. }
  forward_if
  (PROP ( )
   LOCAL (temp _t'12 nullval; temp _tmp_buf md';
   temp _out (Vptr b i); temp _in ictx)
   SEP (data_at (fst (fst idata, Tsh)) (tarray tuchar (Int.unsigned ctxsz))
          (map Vint (snd idata)) md;
   field_at osh (Tstruct _env_md_ctx_st noattr) []
     (d, (md', (Vundef, Vint Int.zero))) (Vptr b i);
   data_at (snd (fst idata, Tsh)) (tarray tuchar (Int.unsigned ctxsz))
     (map Vint (snd idata)) md'; EVP_MD_node vals d;
   data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval)))
     ictx)).
    {  elim H; trivial. }
    { forward. entailer!. }
    forward. Exists Int.one. simpl. entailer!.
    apply sepcon_derives. x(*case md<>null, md'<>null: md -> md', pv1 Vundef not null*) admit.
(*case md=nullval: md, pv1=Vundef rather than nullval in octx*)
(*case md<>nullval, md'=nullval: exists m, m in octx, pv1=Vundef not nullval, star data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint (snd idata)) m*)
(*case md<>null, md'<>null: md -> md', pv1 Vundef not null*)
    apply orp_right2. Exists ctxsz. entailer!. 
    eapply derives_trans. apply data_at_memory_block. simpl.
    rewrite Z.mul_1_l, Z.max_r; trivial. apply Int.unsigned_range.
+ (*case d<>d'*)
   admit. 
     
     forward. Exists Int.one; simpl; entailer!. 


IMP1: data_at sh (tarray tuchar (Int.unsigned sz)) d p |--
      mdDATA sh sz ctxsz d p.
data_at ish (Tstruct _env_md_ctx_st noattr) vals ictx
|-- EVP_MD_CTX_node ish vals ictx

Hint Rewrite @lseg_eq using reflexivity: norm.
EVP_MD_node vals d

     replace_SEP 1 (mdDATA (fst idata) ctxsz (map Vint (snd idata)) md).
       
     rewrite sepcon_assoc. rewrite sepcon_comm.
     apply sepcon_derives.
     * unfold 
    unfold mdDATA; simpl.
     xunfold EVP_MD_NNnode. xold_go_lower.
    simpl. admit. (*def of md'POST*)
    + trivial. entailer. cancel.
        apply orp_left.
      thaw MD'. destruct (Val.eq nullval d'); entailer!.
      * apply orp_right2. unfold EVP_MD_CTX_NNnode. entailer!. 
      * apply orp_right2. unfold EVP_MD_CTX_NNnode. entailer!.

    rewrite if_false. 2: destruct md; try contradiction; discriminate.
    entailer!. simpl. rewrite H2ctxsize; trivial.
    apply orp_right2. Exists iish. entailer!. }
      forward.
      apply  
Ah, distinction md' ?=null alos relevant in case d=d'.
    apply sepcon_valid_pointer2. 
      
       simpl in H. unfold typed_true in H. simpl in H.
   unfold EVP_MD_NNnode. simpl in ; subst.
     (*should be ok, essentially *) subst.
      forward. 
    destruct vals  data_at sh (Tstruct _env_md_st noattr) vals d; .
 apply semax_or. unfold  EVP_MD_node. forward.
    apply sepcon_valid_pointer1. 
    apply sepcon_valid_pointer1. 
  apply sepcon_valid_pointer1. 
    apply EVP_MD_NNnode_validptr. 
  forward_if 
 apply prop_right.
    red in H; simpl in H. red; simpl. intuition.
    red. destruct octx; simpl in *; try contradiction; trivial; simpl in *.
    unfold align_attr.
      rewrite data_at__isptr. Intros. destruct octx; try contradiction.
  unfold data_at_, field_at_. simpl. forward. (*continue.*) admit.
+ Intros vals' ctxsz'. 
forward_call (octx, osh, md', pv1', 
  @inr unit (prod val (reptype (Tstruct _env_md_st noattr))) (d', vals')).
- assert (FR: Frame = [data_at sh (Tstruct _env_md_st noattr) vals d;
              data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (pv1, nullval))) ictx]); subst Frame. reflexivity.
  clear FR; simpl. entailer. Exists ctxsz'. entailer. cancel.
  apply 
  unfold EVP_MD_node. unfold EVP_MD_CTX_NNnode. entailer!.
  unfold EVP_MD_node. Exists sh. entailer. cancel. apply orp_right1; trivial.
- (*continue.*) admit.
forward_if 
  (PROP ( )
   LOCAL (temp _t'25 d; temp _t'24 d'; 
          temp _tmp_buf (if Val.eq d d' then md' else Vint (Int.repr 0));
   temp _out octx; temp _in ictx)
   SEP (data_at sh (Tstruct _env_md_st noattr) vals d;
   data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (pv1, nullval))) ictx;
   data_at osh (Tstruct _env_md_ctx_st noattr) (d', (if Val.eq d d' then nullval else md', (pv1', nullval))) octx;
   (*(*valid_pointer d'*) if Val.eq d d' then emp else EX vals':_, (EX ctxsz' : int,
     !! (get_ctxsize vals' = Vint ctxsz' /\
         Int.eq ctxsz' Int.zero = false) && EVP_MD_NNnode vals' d'*) FRZL FR1)).
{ (*boolean condition evaluates*)
  clear H. destruct d; try contradiction.
  destruct (Val.eq (Vptr b i) d').
  { subst. entailer!. }
  normalize. thaw FR1. 
  apply denote_tc_test_eq_split. normalize.
  apply sepcon_valid_pointer1. 
  apply sepcon_valid_pointer1. 
  apply sepcon_valid_pointer1. 
  apply sepcon_valid_pointer1. 
    apply EVP_MD_NNnode_validptr. 
  apply sepcon_valid_pointer1. entailer!. }
{ (*left branch*)
  forward. forward.
  destruct d; try contradiction. entailer.
  destruct d'; try contradiction; simpl in *.
  { unfold typed_true, sem_cmp_pp, Val.of_bool in H. simpl in H. 
    remember (Int.eq i0 Int.zero) as q. destruct q; try solve [inv H]. }
  { unfold typed_true, sem_cmp_pp, Val.of_bool in H. simpl in H. 
    remember (eq_block b0 b) as q. destruct q; try solve [inv H]; subst.
    remember (Int.eq i0 i) as qq. destruct qq; try solve [inv H].
    apply binop_lemmas2.int_eq_true in Heqqq. subst; simpl in *.
  rewrite 3 if_true; trivial. entailer. } }
{ (*right branch*)
  destruct (Val.eq d d'); subst.  
  + destruct d'; try contradiction.
    unfold typed_false, sem_cmp_pp in H; simpl in H.
    destruct (eq_block b b); try solve [inv H].
    rewrite Int.eq_true in H; inv H.
  + Intros vals'. forward. entailer. Exists vals' ctxsz'. entailer!. }
(*Continuation after conditional*)
destruct (Val.eq d d'); subst.
+
forward_call (octx, osh, nullval, pv1', 
  @inr unit (prod val (reptype (Tstruct _env_md_st noattr))) (d', vals)).
- assert (FR: Frame = [data_at ish (Tstruct _env_md_ctx_st noattr)
  (d', (md, (pv1, pv2))) ictx]); subst Frame. reflexivity.
  clear FR; simpl. entailer. Exists ctxsz. unfold EVP_MD_CTX_NNnode. entailer!.
  unfold EVP_MD_NNnode. Exists sh. entailer. cancel. apply orp_right1; trivial.
- (*continue.*) admit.
+ Intros vals' ctxsz'. 
forward_call (octx, osh, md', pv1', 
  @inr unit (prod val (reptype (Tstruct _env_md_st noattr))) (d', vals')).
- assert (FR: Frame = [data_at sh (Tstruct _env_md_st noattr) vals d;
              data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (pv1, pv2))) ictx]); subst Frame. reflexivity.
  clear FR; simpl. entailer. Exists ctxsz'. entailer. cancel.
  apply 
  unfold EVP_MD_node. unfold EVP_MD_CTX_NNnode. entailer!.
  unfold EVP_MD_node. Exists sh. entailer. cancel. apply orp_right1; trivial.
- (*continue.*) admit.

   rewrite sepcon_comm. rewrite ! sepcon_assoc. apply sepcon_derives.
  * unfold EVP_MD_CTX_NNnode. entailer!.
  * apply orp_right2.

Eval compute in reptype (Tstruct _env_md_st noattr).
assert (exists v:(val * (val * (val * (val * (val * (val * (val * val)))))))%type,
  v=vals). exists vals; trivial.
destruct H.
forward_call (octx, osh, nullval, pv1', 
(*  @inl unit (prod val (reptype (Tstruct _env_md_st noattr))) tt).*)
  @inr unit (prod val (reptype (Tstruct _env_md_st noattr))) (d', x)).
 remember (octx, osh, nullval, pv1', 
  @inr unit (prod val (reptype (Tstruct _env_md_st noattr))) (d', vals)) as args.
forward_call (octx, osh, nullval, pv1', 
(*  @inl unit (prod val (reptype (Tstruct _env_md_st noattr))) tt).*)
  @inr unit (prod val (reptype (Tstruct _env_md_st noattr))) (d', vals)).
assert (exists vv
forward_call (octx, osh, if Val.eq d d' then nullval else md', pv1', ctxsz, vals).


  WITH ctx:val, sh:share, mdd:val, pv1:val, 
       other: unit + val * reptype (Tstruct _env_md_st noattr)
       (*ctxsz: int,
       vals:reptype (Tstruct _env_md_st noattr)*)
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
  match other with
   inl _ =>
      PROP (writable_share sh)
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_NNnode sh (nullval, (mdd, (pv1, nullval))) ctx)
  | inr (d,vals) =>
      EX ctxsz:int, 
      PROP (writable_share sh; isptr d; get_ctxsize vals = Vint ctxsz; Int.eq ctxsz Int.zero=false)
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_NNnode sh (d, (mdd, (pv1, nullval))) ctx; 
           EVP_MD_NNnode vals d;
           ((!!(mdd = nullval)&& emp) || memory_block Tsh (Int.unsigned ctxsz) mdd))
  end

{ assert (FR: Frame = 
   [data_at ish (Tstruct _env_md_ctx_st noattr) (d, (md, (pv1, pv2))) ictx;
    if Val.eq d d' then emp else data_at sh (Tstruct _env_md_st noattr) vals d]).
  subst Frame; reflexivity. subst Frame; clear FR.
  unfold EVP_MD_CTX_NNnode; normalize.
  entailer.
  apply andp_right. destruct (Val.eq d d'); entailer!.
  simpl. cancel.
  destruct (Val.eq d d').
  + subst. entailer. apply orp_right2. entailer!.
    unfold EVP_MD_NNnode. normalize. Exists sh. entailer!.
    apply orp_right1; trivial.
  + cancel. Intros vals'.
    apply orp_left; [ solve [apply orp_right1; trivial] | apply orp_right2 ].
    
  destruct (Val.eq d d'). entailer. cancel.
  unfold   WITH ctx:val, sh:share, d:val, mdd:val, pv1:val, ctxsz: int,
       vals:reptype (Tstruct _env_md_st noattr)
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
     2: inv H.
  forward. forward. remember (Val.eq (Vptr b i) (Vptr b0 i0)) as z.
  destruct z.
  + clear Heqz. inv e. entailer.
  + unfold sem_cmp_pp, Val.of_bool in H. simpl in H. 
    destruct (eq_block b0 b); subst; simpl in H.
    - remember (Int.eq i0 i) as q. destruct q; try solve [inv H].
      apply binop_lemmas2.int_eq_true in Heqq. subst; congruence.
    - entailer!. }
      go_lower.
      entailer. unfold typed_true in H.  simpl in H. 2: inv H. ; subst. congruence.
      unfold Val.of_bool in H. rewrite <- Heqz in H.  simpl in H. discriminate. 
  entailer. simpl. unfold Val.eq. ; subst; simpl in H; inv H.
  unfold typed_true, sem_cmp_pp in H1. simpl in H1.
  destruct (eq_block b0 b); subst; simpl in H1. forward. forward. unfold typed_true, sem_cmp_pp, Val.cmpu_bool, force_val in H; simpl in H.
  remember (sem_cmp_pp Ceq d' d) as b; destruct b; simpl in H. . entailer. xclear H. destruct d; try contradiction. destruct d'; simpl in ptrN_d'; try contradiction; subst.
  apply denote_tc_test_eq_split; try apply valid_pointer_null.
  apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
  apply data_at_valid_ptr. intuition. simpl; omega.
  apply denote_tc_test_eq_split; trivial. try apply valid_pointer_null.
  apply sepcon_valid_pointer2. apply sepcon_valid_pointer1.
  apply data_at_valid_ptr. intuition. simpl; omega. intuition. 
    specialize (Int.unsigned_range ctxsz); intros.
    destruct (zeq 0 (Int.unsigned ctxsz)). 2: omega.
    apply int_eq_false_e in CTXsizeNonzero. elim CTXsizeNonzero. unfold Int.zero. 
    rewrite e, Int.repr_unsigned; trivial.
  entailer. destruct D as [d' [md' [pv1' pv2']]].
 entailer!. simpl in *.
Continue here.
erewrite data_at_type_changable with (sh0:=osh) (t2:=(Tstruct _env_md_ctx_st noattr)).
2: trivial.
forward.
 simpl.

 Intros sh. _pointer.
forward.  data_at ish (Tstruct _env_md_ctx_st noattr)
          (d, (md, (pv1, pv2))) ictx; EVP_MD_node vals d;
   data_at osh
     (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr))) D
     octx)). 
  { subst; contradiction. }
  { forward. forward.
    + entailer!. 
      apply denote_tc_test_eq_split; try apply valid_pointer_null.
      apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
      apply orp_left; entailer!. unfold EVP_MD_NNnode; entailer. 
    + entailer. simpl. 
  apply memory_block_valid_ptr. intuition. 
    specialize (Int.unsigned_range ctxsz); intros.
    destruct (zeq 0 (Int.unsigned ctxsz)). 2: omega.
    apply int_eq_false_e in CTXsizeNonzero. elim CTXsizeNonzero. unfold Int.zero. 
    rewrite e, Int.repr_unsigned; trivial.
  apply semax_orp_SEPx; Intros; subst.
{ (*d=nullval*)
  forward. 
  forward_if

OK till here. Next: copy_ex

Definition EVP_MD_CTX_cleanup_SPEC3 := DECLARE _EVP_MD_CTX_cleanup
  WITH ctx:val, sh:share, d:val, mdd:val, pv1:val, pv2:val, ctxsz: int,
       vals:reptype (Tstruct _env_md_st noattr)
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (writable_share sh; pv2=nullval;
            get_ctxsize vals = Vint ctxsz; Int.eq ctxsz Int.zero=false)
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_NNnode sh (d, (mdd, (pv1, pv2))) ctx; EVP_MD_node vals d; 
           (!!(mdd = nullval \/ d=nullval) && emp) || memory_block Tsh (Int.unsigned ctxsz) mdd)
  POST [ tint ]
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.one)))
       SEP (data_at_ sh (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr))) ctx; 
            EVP_MD_node vals d).

Lemma body_EVP_MD_CTX_cleanup3: semax_body Vprog Gprog_cleanup f_EVP_MD_CTX_cleanup EVP_MD_CTX_cleanup_SPEC3.
Proof. 
  start_function. unfold EVP_MD_CTX_NNnode. subst. rename H0 into CTXsize. rename H1 into CTXsizeNonzero. 
  Intros.
  forward. 
  focus_SEP 1.
  apply semax_orp_SEPx; Intros; subst.
{ (*d=nullval*)
  forward_if
  (PROP ( )
   LOCAL (temp _t'1 nullval; temp _ctx ctx)
   SEP (emp;
   data_at sh (Tstruct _env_md_ctx_st noattr)
     (nullval, (mdd, (pv1, nullval))) ctx;
   !! (mdd = nullval) && emp || memory_block Tsh (Int.unsigned ctxsz) mdd)).
  { contradiction. }
  { forward. entailer!. }
  forward_if 
  (PROP ( )
   LOCAL (temp _t'2 nullval; temp _ctx ctx)
   SEP (emp;
   data_at sh (Tstruct _env_md_ctx_st noattr)
     (nullval, (mdd, (pv1, nullval))) ctx;
   !! (mdd = nullval) && emp || memory_block Tsh (Int.unsigned ctxsz) mdd)).
   { elim H; trivial. }
   { forward. entailer!. }
   forward_if 
  (PROP ( )
   LOCAL (temp _ctx ctx)
   SEP (emp;
   data_at sh (Tstruct _env_md_ctx_st noattr)
     (nullval, (mdd, (pv1, nullval))) ctx;
   !! (mdd = nullval) && emp || memory_block Tsh (Int.unsigned ctxsz) mdd)).
   { elim H; trivial. }
   { forward. entailer!. }
   forward.
   forward_if 
  (PROP ( )
   LOCAL (temp _ctx ctx)
   SEP (emp;
   data_at sh (Tstruct _env_md_ctx_st noattr)
     (nullval, (mdd, (pv1, nullval))) ctx;
   !! (mdd = nullval) && emp || memory_block Tsh (Int.unsigned ctxsz) mdd)).
   { contradiction. }
   { forward. entailer!. }
   forward_call (ctx, sh, sizeof (Tstruct _env_md_ctx_st noattr)).
   forward.
   cancel. unfold EVP_MD_node.  apply orp_right1. entailer!.
   
  apply 
  forward_if (
   PROP ( )
   LOCAL (temp _t'1 (if Val.eq d nullval then Vint Int.zero else Vint Int.one); 
          temp _t'12 d; temp _ctx ctx)
   SEP (data_at sh (Tstruct _env_md_ctx_st noattr) 
          (d, (mdd, (pv1, nullval))) ctx; EVP_MD_node vals d;
   !! (mdd = nullval) && emp || memory_block Tsh (Int.unsigned ctxsz) mdd)).
{ clear H. 
  apply denote_tc_test_eq_split; try apply valid_pointer_null.
  destruct d; simpl in PNd; try contradiction; subst. apply valid_pointer_null.
  apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
  apply orp_left; entailer!. discriminate. apply EVP_MD_NNnode_validptr. }
{ clear PNd; rename H into PNd.
  replace_SEP 1 (EVP_MD_NNnode vals d).
  { entailer. apply orp_left; normalize. }
  unfold EVP_MD_NNnode; Intros sh1. rename H into Rsh1.
  destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *. subst.
  forward. forward. forward. entailer!.
  rewrite if_false. 2: destruct d; try contradiction; discriminate.
  simpl. rewrite CTXsizeNonzero; trivial. 
  unfold EVP_MD_node, EVP_MD_NNnode. apply orp_right2. Exists sh1. entailer!. }
{ subst. forward. entailer!. }
  forward_if 
  (PROP ( )
   LOCAL (temp _t'2 (if Val.eq d nullval then Vint Int.zero else if Val.eq mdd nullval then Vint Int.zero else Vint Int.one); 
          temp _t'1 (if Val.eq d nullval then Vint Int.zero else Vint Int.one);
          temp _t'12 d; temp _ctx ctx)
   SEP (data_at sh (Tstruct _env_md_ctx_st noattr)
          (d, (mdd, (pv1, nullval))) ctx; EVP_MD_node vals d;
        !! (mdd = nullval) && emp || memory_block Tsh (Int.unsigned ctxsz) mdd)).
{ destruct d; simpl in PNd; try contradiction; subst. rewrite if_true in H; trivial. inv H.
  clear H. rewrite if_false; try discriminate.
  forward. forward. 
  + entailer.
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer2.
    apply orp_left; normalize. apply valid_pointer_null.
    apply memory_block_valid_ptr. intuition.
    specialize (Int.unsigned_range ctxsz); intros.
    destruct (zeq 0 (Int.unsigned ctxsz)). 2: omega.
    apply int_eq_false_e in CTXsizeNonzero. elim CTXsizeNonzero. unfold Int.zero. 
    rewrite e, Int.repr_unsigned; trivial.
  + rewrite if_false; try discriminate. entailer.
    destruct mdd; simpl in PNmdd; try contradiction; subst; simpl.
    - rewrite if_true; trivial; simpl. entailer!.
    - rewrite if_false; [ entailer! | discriminate]. }
{ destruct d; simpl in PNd; try contradiction; subst.
  - clear H. forward. entailer!.
  - rewrite if_false in H; try discriminate. }
focus_SEP 1.
apply semax_orp_SEPx; Intros; subst.
+ rewrite 2 if_true ; trivial.
  forward_if 
  (PROP ( )
   LOCAL (temp _ctx ctx)
   SEP (
   data_at sh (Tstruct _env_md_ctx_st noattr)
     (nullval, (mdd, (pv1, nullval))) ctx(*;
   !! (mdd = nullval) && emp || memory_block Tsh (Int.unsigned ctxsz) mdd*))). 
  { elim H; trivial. } 
  { forward. entailer. } 
  focus_SEP 1. apply semax_orp_SEPx; Intros; subst.
  - forward.
    forward_if (PROP ( )
     LOCAL (temp _ctx ctx)
     SEP (data_at sh (Tstruct _env_md_ctx_st noattr) (nullval, (nullval, (pv1, nullval))) ctx)).
    { simpl in H; contradiction. }
    { forward. entailer!. }
    forward_call (ctx, sh, sizeof (Tstruct _env_md_ctx_st noattr)).
    forward.
    cancel. apply orp_right1. entailer!.
  - forward.
    forward_if (PROP ( )
      LOCAL (temp _ctx ctx)
      SEP (memory_block Tsh (Int.unsigned ctxsz) mdd;
           data_at sh (Tstruct _env_md_ctx_st noattr) (nullval, (mdd, (pv1, nullval))) ctx)).
    { simpl in H; contradiction. }
    { forward. entailer!. }
    forward_call (ctx, sh, sizeof (Tstruct _env_md_ctx_st noattr)).
    forward.
    cancel. apply orp_right1. entailer!.
    
   
      data_at sh (Tstruct _env_md_ctx_st noattr) (d, (mdd, (pv1, nullval))) ctx; 
   EVP_MD_node vals d;
   !! (mdd = nullval) && emp || memory_block Tsh (Int.unsigned ctxsz) mdd)).
+ unfold typed_true in H.
(*  clear H. *)forward. forward.
  focus_SEP 1. 
  apply semax_orp_SEPx; Intros; subst.
  - (*d=null*)
    rewrite if_true in H; trivial; simpl in H. inv H.
  - (*d=ptr*) unfold EVP_MD_NNnode. Intros sh1. rename H0 into Rsh1.
    rewrite data_at_isptr; Intros. 
    rewrite if_false in H. 2: destruct d; try contradiction; discriminate.
    rewrite if_false. 2: destruct d; try contradiction; discriminate.
    destruct (Val.eq mdd nullval); simpl in H; try solve [inv H]. clear H.
    focus_SEP 2. apply semax_orp_SEPx; Intros; subst; try congruence.
    rewrite if_false. 2: destruct d; try contradiction; discriminate.
    destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]].
    simpl in type, mds, flags, ini, upd, fin, blsize, ctxsize, CTXsize; subst.
    forward.
    forward_call (mdd,  Tsh, Int.unsigned ctxsz).
    { simpl. rewrite Int.repr_unsigned. entailer!. }
    { split. apply writable_share_top. apply Int.unsigned_range_2. }
    forward.
    forward_call (mdd, Int.unsigned ctxsz).
    rewrite sepcon_assoc. apply sepcon_derives. 
    { eapply derives_trans. apply data_at_memory_block. simpl. rewrite Z.mul_1_l, Z.max_r; trivial.
      apply Int.unsigned_range. }
    { cancel. }
    entailer!. apply orp_right2. Exists sh1. entailer!.
+ focus_SEP 1. 
  apply semax_orp_SEPx; Intros; subst.
  - (*d=null*)
    clear H. rewrite 2 if_true; trivial.
    focus_SEP 2. apply semax_orp_SEPx; Intros; subst.
    forward.
    { entailer. cancel. apply orp_right1. entailer!. }
    forward.
    entailer. cancel. 
  - left.
    entailer. unfold EVP_MD_NNnode. Exists  unfold typed_false in H; simpl in H. simpl in H inv H. inv H.
+ forward.
  forward_if (PROP ( )
   LOCAL (temp _t'3 nullval; temp _ctx ctx)
   SEP (data_at sh (Tstruct _env_md_ctx_st noattr)
          (d, (mdd, (pv1, nullval))) ctx;
   EVP_MD_NNnode vals d)).
  { contradiction. }
  { clear H. forward. entailer!. }
  forward_call (ctx, sh, sizeof (Tstruct _env_md_ctx_st noattr)).
  forward.
Time Qed. (*Slow; > 40s*)

(*Continue here
Parameter contentmodels (*bytes specdata*): list val ->  EVP_MD_CTX -> Prop.

Definition EVP_MD_data_rep (M:EVP_MD)  (C: EVP_MD_CTX) (p:val): mpred :=
  EX sh: share, EX bytes: list val, 
  !!(writable_share sh /\ contentmodels bytes C /\ 
     forall m, ctx_configured C = Some m -> m=M) && 
  data_at sh (tarray tuchar (EVP_MD_rec_ctx_size XX) bytes p.

Lemma EVP_MD_data_rep_isptrornull M C p: EVP_MD_data_rep M C p |-- !! is_pointer_or_null p.
Proof. unfold EVP_MD_data_rep. Intros sh bytes. entailer!. Qed.
Lemma EVP_MD_data_rep_isptrornull' M C p: EVP_MD_data_rep M C p = (!!(is_pointer_or_null p) && EVP_MD_data_rep M C p).
Proof. apply pred_ext; entailer. apply EVP_MD_data_rep_isptrornull. Qed.

Lemma EVP_MD_data_rep_validptr M C p: EVP_MD_data_rep M C p |-- valid_pointer p.
Proof. unfold EVP_MD_data_rep. Intros sh bytes. entailer. Qed. 

Definition EVP_MD_CTX_rep (M: EVP_MD) (C: EVP_MD_CTX) (vals:reptype (Tstruct _env_md_ctx_st noattr)) :=
match vals with (md, (mddata, _)) => (*TODO:pctx not yet modeled*)
EX r: EVP_MD_record, 
!!(get_md_record M = Some r)
&& (EVP_MD_rep r md * EVP_MD_data_rep M C mddata)
end.
(*
Definition EVP_MD_CTX_rep (C: EVP_MD_CTX) (p:val):mpred :=
  EX sh:_, EX vals :_,
  !!readable_share sh &&
  (matchEVP_MD_CTX C vals * data_at sh (Tstruct _env_md_ctx_st noattr) vals p).
*)
(*
Definition EVP_MD_CTX_rep' (C: EVP_MD_CTX) (d p:val):mpred :=
  EX sh:_, EX mddata :val, EX pctx:val*val,
  !!readable_share sh &&
  (EVP_MD_data_rep C mddata * data_at sh (Tstruct _env_md_ctx_st noattr) (d,(mddata,pctx)) p).
*)


(******************************************************************************)

(*Comment: digest.h does not say what happens if digest is not set (ie ctx->digest=null), or indeed
  if the context is not in the right state.
  In contrast, sthe DigestOperationAccessors are specified to crash in such a case.*)
Definition EVP_DigestUpdate_SPEC := DECLARE _EVP_DigestUpdate
  WITH ctx:val, data:_, len:Z, M: EVP_MD, olddata:list data, bytes:list data, d:val, x:val * (val * val), sh:share
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)), 
        _data OF (tptr tvoid), _len OF tuint ]
      PROP (readable_share sh)
      LOCAL (temp _ctx ctx; temp _data data; temp _len (Vint (Int.repr len)))
      SEP (EVP_MD_CTX_rep M (EVP_MD_CTX_hashed M olddata) (d, x) ctx;
           data_at sh (tarray tuchar (Z.to_nat len) noattr) bytes data)
  POST [ tint ]
       PROP ()
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (EVP_MD_CTX_rep M (EVP_MD_CTX_hashed M (olddata++bytes)) (d, x) ctx;
            data_at sh (tarray tuchar (Z.to_nat len) noattr) bytes data).

Definition EVP_sha256_do_init_SPEC := DECLARE _EVP_sha256_do_init
  WITH out:val, sh:share, ini:val, upd:val, fin:val
  PRE [ _out OF tptr (Tstruct _env_md_st noattr) ]
     PROP (writable_share sh)
     LOCAL (temp _out out;
(*            temp _sha256_init ini; *)gvar _sha256_init ini; 
            gvar _sha256_update upd; gvar _sha256_final fin)
     SEP (data_at_ sh (Tstruct _env_md_st noattr) out *
          func_ptr' (init_spec_of_NID NID_sha256) ini *
          func_ptr' (update_spec_of_NID NID_sha256) upd *
          func_ptr' (final_spec_of_NID NID_sha256) fin)
  POST [ tvoid ]
    PROP () 
    LOCAL ((*gvar _sha256_init ini; gvar _sha256_update upd; gvar _sha256_final fin*))
    SEP (data_at_ sh (Tstruct _env_md_st noattr) out *
          func_ptr' (init_spec_of_NID NID_sha256) ini *
          func_ptr' (update_spec_of_NID NID_sha256) upd *
          func_ptr' (final_spec_of_NID NID_sha256) fin).



(* Spec in digest.h: EVP_MD_CTX_cleanup frees any resources owned by |ctx| and resets it to a
                     freshly initialised state. It does not free |ctx| itself. It returns one. 
  Comment: spec doesn't say what happens if ctx==null (our preconditions uses reequires NNode)*)
(*TODO: currently, we're not modeling/using pctx, so precondition here requires ctx->pctx==null and 
  ctx->pctx_ops==null*)
Definition EVP_MD_CTX_cleanup_SPEC := 
  let n := sizeof (Tstruct _env_md_ctx_st noattr) 
  in DECLARE _EVP_MD_CTX_cleanup
   WITH ctx:val, C:EVP_MD_CTX, d: val, mdd:val
   PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
       PROP ()
       LOCAL (temp _ctx ctx)
       SEP (EVP_MD_CTX_NNnode C (d, (mdd,(nullval,nullval))) ctx; matchEVP_MD_CTX C (d,(mdd,(nullval,nullval))))
   POST [ tint ]
     EX sh:share,
       PROP (readable_share sh)
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (data_at sh (tarray tuchar n) (list_repeat (Z.to_nat n) (Vint Int.zero)) ctx;
            EVP_MD_rep (digest_of_ctx C) d).

Definition Gprog : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]).*)
  [OPENSSL_memcpy_SPEC; OPENSSL_memset_SPEC;OPENSSL_malloc_SPEC;
   EVP_sha256_do_init_SPEC; EVP_DigestUpdate_SPEC; 
   EVP_MD_CTX_cleanup_SPEC; EVP_MD_CTX_init_SPEC; EVP_MD_CTX_create_SPEC; EVP_MD_CTX_block_size_SPEC; EVP_MD_CTX_type_SPEC; 
   EVP_MD_CTX_size_SPEC; EVP_MD_CTX_md_SPEC; EVP_MD_type_SPEC; EVP_MD_flags_SPEC; EVP_MD_size_SPEC; EVP_MD_block_size_SPEC].

Lemma body_EVP_MD_CTX_cleanup: semax_body Vprog Gprog f_EVP_MD_CTX_cleanup EVP_MD_CTX_cleanup_SPEC.
Proof.
  start_function.
  unfold EVP_MD_CTX_NNnode. Intros sh. rename H into Rsh.
  unfold matchEVP_MD_CTX. rewrite EVP_MD_rep_isptr'. Intros.
  forward.
  unfold EVP_MD_rep. Intros sh2 vals. rename H into Rsh2.
  destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
  simpl in *; Intros.
  forward_if 
    (PROP ( )
     LOCAL (temp _t'1 (Vint
             (if
               Int.eq (Int.repr (EVP_MD_rec_ctx_size (digest_of_ctx C)))
                 Int.zero
              then Int.zero
              else Int.one));
           temp _t'14 (Vint (Int.repr (EVP_MD_rec_ctx_size (digest_of_ctx C))));
           temp _t'13 d; temp _t'12 d; temp _ctx ctx)
     SEP (data_at sh (Tstruct _env_md_ctx_st noattr) (d, (mdd, (nullval, nullval))) ctx;
          func_ptr' (init_spec_of_NID (EVP_MD_rec_type (digest_of_ctx C))) ini;
          func_ptr' (update_spec_of_NID (EVP_MD_rec_type (digest_of_ctx C))) upd;
          func_ptr' (final_spec_of_NID (EVP_MD_rec_type (digest_of_ctx C))) fin;
          data_at sh2 (Tstruct _env_md_st noattr) (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) d;
          EVP_MD_data_rep C mdd)).
  { clear H. forward. forward. forward. entailer!. } 
  { subst d; contradiction. }
  rewrite EVP_MD_data_rep_isptrornull'; Intros.
  forward_if 
    (PROP ( )
     LOCAL ( temp _t'2 (if
                 Int.eq (Int.repr (EVP_MD_rec_ctx_size (digest_of_ctx C)))
                   Int.zero
                then Vint Int.zero
                else if Val.eq mdd nullval then Vint Int.zero else Vint Int.one);
             temp _t'1 (Vint
             (if
               Int.eq (Int.repr (EVP_MD_rec_ctx_size (digest_of_ctx C)))
                 Int.zero
              then Int.zero
              else Int.one));
           temp _t'14 (Vint (Int.repr (EVP_MD_rec_ctx_size (digest_of_ctx C))));
           temp _t'13 d; temp _t'12 d; temp _ctx ctx)
     SEP (data_at sh (Tstruct _env_md_ctx_st noattr) (d, (mdd, (nullval, nullval))) ctx;
          func_ptr' (init_spec_of_NID (EVP_MD_rec_type (digest_of_ctx C))) ini;
          func_ptr' (update_spec_of_NID (EVP_MD_rec_type (digest_of_ctx C))) upd;
          func_ptr' (final_spec_of_NID (EVP_MD_rec_type (digest_of_ctx C))) fin;
          data_at sh2 (Tstruct _env_md_st noattr) (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) d;
          EVP_MD_data_rep C mdd)).
  { remember (Int.eq (Int.repr (EVP_MD_rec_ctx_size (digest_of_ctx C))) Int.zero) as b. destruct b; try solve [congruence].
    clear H4.
    forward. old_go_lower. entailer!.
    forward.
    - old_go_lower. entailer.
      apply denote_tc_test_eq_split. apply sepcon_valid_pointer2. apply EVP_MD_data_rep_validptr.
      apply valid_pointer_null.
    -subst. destruct mdd; try solve [contradiction]; simpl in PNmdd; subst. 
     * old_go_lower. entailer!.
     * old_go_lower. entailer!. } 
  { remember (Int.eq (Int.repr (EVP_MD_rec_ctx_size (digest_of_ctx C))) Int.zero) as b. destruct b; try solve [discriminate].
    clear PNd H4.
    forward. old_go_lower. entailer!. }
(*OK till here*)

  forward_if 
    (PROP ( )
     LOCAL (temp _t'14 (Vint (Int.repr (EVP_MD_rec_ctx_size (digest_of_ctx C))));
           temp _t'13 d; temp _t'12 d; temp _ctx ctx)
     SEP (data_at sh (Tstruct _env_md_ctx_st noattr) (d, (mdd, (nullval, nullval))) ctx;
          func_ptr' (init_spec_of_NID (EVP_MD_rec_type (digest_of_ctx C))) ini;
          func_ptr' (update_spec_of_NID (EVP_MD_rec_type (digest_of_ctx C))) upd;
          func_ptr' (final_spec_of_NID (EVP_MD_rec_type (digest_of_ctx C))) fin;
          data_at sh2 (Tstruct _env_md_st noattr) (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) d;
          EVP_MD_data_rep C mdd)).
   { forward. old_go_lower. entailer!.
     forward. old_go_lower. entailer!.
     forward. old_go_lower. entailer. 
     drop_LOCAL 3%nat.
     drop_LOCAL 3%nat.
     unfold EVP_MD_data_rep. Intros sh3 bytes.
     assert (XVALS: exists xvals: reptype (Tstruct _env_md_ctx_st noattr), xvals = (d, (mdd, (nullval,nullval)))). eexists; reflexivity.
     destruct XVALS as [xvals XVals].
     assert (YVALS: exists yvals:reptype (Tstruct _env_md_st noattr), yvals= (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize)))))))). eexists; reflexivity.
     destruct YVALS as [yvals YVals].
Parameter PP:environ -> mpred.
apply semax_post with (R':=(overridePost
  (PROP ( )
   LOCAL (temp _t'10 ctxsize; temp _t'9 d; temp _t'8 mdd;
   temp _t'14 (Vint (Int.repr (EVP_MD_rec_ctx_size (digest_of_ctx C))));
   temp _t'13 d; temp _t'12 d; temp _ctx ctx)
   SEP (data_at sh (Tstruct _env_md_ctx_st noattr)
          xvals ctx;
   func_ptr' (init_spec_of_NID (EVP_MD_rec_type (digest_of_ctx C))) ini;
   func_ptr' (update_spec_of_NID (EVP_MD_rec_type (digest_of_ctx C))) upd;
   func_ptr' (final_spec_of_NID (EVP_MD_rec_type (digest_of_ctx C))) fin;
   data_at sh2 (Tstruct _env_md_st noattr) yvals d;
   data_at_ sh3 (tarray tuchar (EVP_MD_rec_ctx_size (digest_of_ctx C))) mdd))) (normal_ret_assert PP)).
     2: admit. (*forward_call (mdd, sh3, EVP_MD_rec_ctx_size (digest_of_ctx C)).*)
   intros. unfold POSTCONDITION, abbreviate, overridePost, normal_ret_assert, EVP_MD_data_rep.
   old_go_lower.  
   destruct (eq_dec ek EK_normal); subst. 
   + simpl. entailer. Exists sh3; entailer. admit.
   + rewrite 2 if_false; trivial. normalize. }

  {  forward. old_go_lower. entailer!. }
x
  forward. old_go_lower. entailer. admit. (*is_pointer_or_null pctxops*) unfold normal_ret_assert. Intros.  normalize. simpl. repr (EVP_MD_rec_ctx_size (digest_of_ctx C))).
  
    discriminate. } forward. old_go_lower. entailer. subst d; contradiction. }


Lemma body_EVP_sha256_do_init: semax_body Vprog Gprog f_EVP_sha256_do_init EVP_sha256_do_init_SPEC.
Proof.
  start_function. 
  rewrite (func_ptr'_isptr' ini).
  rewrite (func_ptr'_isptr' upd). 
  rewrite (func_ptr'_isptr' fin).
  rewrite data_at__isptr. normalize.
  forward. simpl.
  forward.
  forward. 
  destruct ini; try contradiction.
  destruct upd; try contradiction.
  destruct fin; try contradiction. 
  destruct out; try contradiction.
  simpl. normalize.
  forward. old_go_lower. entailer!. admit. (*typecheck_error (var_not_in_tycontext Delta _sha256_init)*)
  forward. admit.
  forward. admit.
  forward. forward. old_go_lower. entailer.
  Eval compute in (complete_type cenv_cs (Tstruct _sha256_state_st noattr)).
Print Esizeof.
Locate _sha256_state_st. admit.
  simpl.
  deadvars!. 
  drop_LOCAL 0%nat. (*ini*)
  drop_LOCAL 0%nat. (*upd*)
  drop_LOCAL 0%nat. (*fin*)
  forward. (*cancel. apply andp_right. admit.
  apply sepcon_derives. 2: cancel.   apply sepcon_derives. 2: cancel. apply sepcon_derives. 2: cancel.*)
  rewrite field_at_data_at. simpl.
  rewrite field_address_offset by auto with field_compatible. simpl.
  rewrite Int.add_zero. cancel.

  rewrite offset_val_zero_Vptr.
apply data_at_data_at_. cancel. entailer. 
   cancel. entailer. unfold POSTCONDITION, abbreviate.
  unfold frame_ret_assert, function_body_ret_assert . normalize.
eapply semax_post. 2: forward. simpl. simpl. forward.
  drop_LOCAL forward.
eapply semax_pre_post with (P':=PROP ( )
   LOCAL (temp _out out) SEP() ). Focus 3.  forward. unfold func_ptr'.
destruct ini.
 normalize.  forward. entailer. 

f_EVP_sha256_do_init
Record myPRE:Type := mkmyPre
  { pretype: rmaps.TypeTree;
    precond: forall ts : list Type,
             functors.MixVariantFunctor._functor
              (rmaps.dependent_type_functor_rec ts (AssertTT pretype)) mpred;
    sneprecond: @super_non_expansive pretype precond}.
Record myPOST:Type := mkmyPost
  { posttype: rmaps.TypeTree;
    postcond: forall ts : list Type,
             functors.MixVariantFunctor._functor
              (rmaps.dependent_type_functor_rec ts (AssertTT posttype)) mpred;
    snepostcond: @super_non_expansive posttype postcond}.

Definition mypred C p:mpred :=
  EX d:_, EX mdd:_, EX x:_,
           (EVP_MD_CTX_NNnode C (d, (mdd,x)) p *  EVP_MD_rep (digest_of_ctx C) d).

Definition sha256Upd_TypeTree:rmaps.TypeTree := rmaps.ProdType (rmaps.ConstType EVP_MD_CTX ) (rmaps.ConstType val).
(*Parameter sha256Upd_PRE:forall ts : list Type,
             functors.MixVariantFunctor._functor
              (rmaps.dependent_type_functor_rec ts (AssertTT sha256Upd_TypeTree)) mpred.*)
Definition sha256Upd_PRE:forall ts : list Type,
             functors.MixVariantFunctor._functor
              (rmaps.dependent_type_functor_rec ts (AssertTT sha256Upd_TypeTree)) mpred :=

Parameter sha256Upd_SNEpre: @super_non_expansive sha256Upd_TypeTree sha256Upd_PRE.
Parameter sha256Upd_POST:forall ts : list Type,
             functors.MixVariantFunctor._functor
              (rmaps.dependent_type_functor_rec ts (AssertTT sha256Upd_TypeTree)) mpred.
Parameter sha256Upd_SNEpost: @super_non_expansive sha256Upd_TypeTree sha256Upd_POST.

Definition sha256upd_spec: funspec.
eapply mk_funspec.
apply (semax.fn_funsig f_sha256_update). 
apply cc_default.
apply sha256Upd_SNEpre.
apply sha256Upd_SNEpost.
Defined.

Definition updPre C:
update_spec_of_NID (EVP_MD_rec_type (digest_of_ctx C)) =sha256upd_spec.
Admitted.

Lemma body_EVP_DigestUpdate: semax_body Vprog Gprog f_EVP_DigestUpdate EVP_DigestUpdate_SPEC.
Proof.
  start_function. 
  rewrite  EVP_MD_CTX_NNnode_isptr'; Intros.
  unfold EVP_MD_CTX_NNnode. destruct x as [mdd [pctx pctxops]]. Intros sh. rename H into Rsh. 
  forward.
  unfold EVP_MD_rep. Intros sh2.
  assert (exists vals: reptype (Tstruct _env_md_ctx_st noattr), vals = (d, (mdd, (pctx, pctxops)))).
     eexists; reflexivity.
  destruct H as [myvals Vals].
  apply (semax_pre (EX vals : reptype (Tstruct _env_md_st noattr),
    PROP (readable_share sh2)
    LOCAL (temp _t'1 d; temp _ctx ctx; temp _data data; temp _len len)
    SEP (data_at sh (Tstruct _env_md_ctx_st noattr) myvals ctx;
         matchEVP_MD_record (digest_of_ctx C) vals;
         data_at sh2 (Tstruct _env_md_st noattr) vals d))); subst.
  { entailer!. Exists vals. entailer!. }
  Intros vals. rename H into Rsh2.
  destruct vals as [type [mdsize  [flags [ini [upd [fin [blocksize ctxsizsimpl]]]]]]]. 
  simpl in *. Intros.
  forward. rewrite updPre.
  forward_call (3).
Check f_sha256_update. Print function. Search base.funsig. 
Eval compute in (semax.fn_funsig f_sha256_update).
remember (update_spec_of_NID (EVP_MD_rec_type (digest_of_ctx C))) as UPDSPEC.
destruct UPDSPEC.
update_spec_of_NID (EVP_MD_rec_type (digest_of_ctx C)) =
  mk_funspec (semax.fn_funsig f_sha256_update) cc_default
   cancel.  apply extract_exists_in_SEP. normalize. Intros.
  unfold_data_at 1%nat.
  forward.
  forward_call (ctx, C, d, x).
    apply sepcon_derives; [apply orp_right2; trivial | cancel]. 
  rewrite if_false by (destruct ctx; try contradiction; discriminate).
  forward_call (d, digest_of_ctx C).


Existing Instance NullExtension.Espec.

Lemma all_funcs_correct:
  semax_func Vprog Gprog [](*(prog_funct prog)*) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
eapply semax_func_cons.
semax_func_cons body_EVP_MD_type. apply semax_func_cons_malloc_aux.
semax_func_cons body_free.
semax_func_cons body_exit.


simpl.
  rewrite data_at_isptr. Intros. destruct md; try contradiction. clear Pmd.
  unfold_data_at (1%nat). forward. forward.
  eapply semax_post.
  Focus 2. forward.  unfold_data_at (1%nat).
  forward.
Lemma body_EVP_MD_type: semax_body Vprog Gprog f_EVP_MD_type EVP_MD_type_SPEC. 
Proof.
  start_function. 
  unfold EVP_MD_rep. Intros sh vals; rename H into Rsh.
  destruct vals as (type, (mdsize, (flags, (ini, (upd, (fin, (blocksize, ctxsize))))))). simpl in *.
  Intros. 
  rewrite data_at_isptr. Intros. destruct md; try contradiction. clear Pmd.
  unfold_data_at (1%nat).
  forward.
Lemma change_compspecs_t_struct_SHA256state_st:
  @data_at spec_sha.CompSpecs Tsh t_struct_SHA256state_st =
  @data_at CompSpecs Tsh t_struct_SHA256state_st.
  unfold EVP_MD_rep. 
  Exists sh (Vint (Int.repr (NID_of_DigestNID (EVP_MD_rec_type R))),
       (Vint (Int.repr (EVP_MD_rec_md_size R)),
       (Vint (Int.repr (EVP_MD_rec_flags R)),
       (ini,
       (upd,
       (fin,
       (Vint (Int.repr (EVP_MD_rec_block_size R)),
       Vint (Int.repr (EVP_MD_rec_ctx_size R))))))))). 
  simpl. entailer!. (type, (mdsize, (flags, (ini, (upd, (fin, (blocksize, ctxsize))))))). simpl. destruct vals. simpl in *. rewrite extract_exists_in_SEP. apply extract_exists_pre; intros rsh.
  rewrite extract_exists_in_SEP. apply extract_exists_pre; intros E.
  erewrite extract_prop_in_SEP. Intros.
    normalize.
   Intros. _exists. normalize.

Definition EVP_MD_CTX_rep (p:val):mpred :=
  EX sh:_, 
  !!readable_share sh &&
  data_at sh sh (Tstruct _env_md_ctx_st noattr)
*)
*)