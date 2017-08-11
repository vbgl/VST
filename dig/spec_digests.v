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
      (R1 R2 : mpred) (T : ret_assert) (c : statement)
  (HR1 : semax Delta
         (PROPx P (LOCALx Q (SEPx (cons R1 nil)))) c T)
  (HR2 : semax Delta
         (PROPx P (LOCALx Q (SEPx (cons R2 nil)))) c T):
semax Delta
  (PROPx P (LOCALx Q (SEPx (cons (orp R1 R2) nil)))) c T.
Proof.
 eapply semax_pre; [| apply (semax_orp HR1 HR2)].
 old_go_lower. normalize. 
(* destruct Q; solve 
   [ apply orp_left; [apply orp_right1| apply orp_right2]; entailer! ].*)
Qed.
Lemma semax_orp_SEP cs Espec Delta P Q R1 R2 T c
  (HR1: @semax cs Espec Delta (PROP (P) LOCAL (Q) SEP (R1)) c T)
  (HR2: @semax cs Espec Delta (PROP (P) LOCAL (Q) SEP (R2)) c T):
  @semax cs Espec Delta (PROP (P) LOCAL (Q) SEP (R1 || R2)) c T.
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

(*Taken from spec_sha TODO: adapt to OPENSSL's code, and verify the body (code is included in digest.v)*)
Definition OPENSSL_memset_SPEC := DECLARE _OPENSSL_memset  
   WITH p: val, sh : share, n: Z, c: int
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tint, 3%positive OF tuint ]
       PROP (writable_share sh; 0 <= n <= Int.max_unsigned)
       LOCAL (temp 1%positive p; temp 2%positive (Vint c);
                   temp 3%positive (Vint (Int.repr n)))
       SEP (memory_block sh n p)
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp p)
       SEP(data_at sh (tarray tuchar n) (list_repeat (Z.to_nat n) (Vint c)) p).

(**** Other functions called from digest.c but not equipped with fucntion bodies in digest.v***) 
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

(*Again taken from verif_bst*)
Definition OPENSSL_free_SPEC := DECLARE _free
  WITH p : val , n : Z
  PRE [ 1%positive OF tptr tvoid , 2%positive OF tint]
     (* we should also require natural_align_compatible (eval_id 1) *)
      PROP() LOCAL (temp 1%positive p; temp 2%positive (Vint (Int.repr n)))
      SEP (memory_block Tsh n p)
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

(*Other functions called from digest.c but clightgen doesn't include fucntion bodies in the 
  generated file:
Definition OPENSSL_PUT_ERROR_SPEC := DECLARE _OPENSSL_PUT_ERROR      *)

(*Forgetting what the content is simplifies the proof - maybe it's also good policy?*)
Definition EVP_MD_CTX_init_SPEC := DECLARE _EVP_MD_CTX_init
   WITH ctx:val, sh:share, n:Z
   PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr) ]
       PROP (writable_share sh; n=sizeof (Tstruct _env_md_ctx_st noattr))
       LOCAL (temp _ctx ctx)
       SEP (data_at_ sh (Tstruct _env_md_ctx_st noattr) ctx)
   POST [ tvoid ]
       PROP ()
       LOCAL ()
       SEP (data_at_ sh (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr))) ctx).

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
       SEP ((*data_at sh (tarray tuchar n) 
             (list_repeat (Z.to_nat n) (Vint Int.zero)) ctx*)
            (!!(ctx=nullval) && emp) || data_at_ Tsh (tarray tuchar (sizeof (Tstruct _env_md_ctx_st noattr))) ctx).

Definition Gprog_EVPMDCTX_1 : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [EVP_MD_CTX_create_SPEC; EVP_MD_CTX_init_SPEC; OPENSSL_memset_SPEC; OPENSSL_malloc_SPEC].

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

Lemma body_EVP_MD_CTX_init: semax_body Vprog Gprog_EVPMDCTX_1 f_EVP_MD_CTX_init EVP_MD_CTX_init_SPEC.
Proof.
  start_function. simpl in *; subst.
  rewrite data_at__memory_block; simpl; Intros.
  forward_call (ctx, sh, 16, Int.zero).
    rewrite int_max_unsigned_eq; split; [trivial | omega].
  time forward. apply data_at_data_at_. 
Qed. 

(****** Specs of the four Digest Operation Accessors. *******)
(*nonnull node*)
Definition EVP_MD_CTX_NNnode (vals:val*(val*(val*val))) (p:val):mpred :=
  match vals with (d, (mddata, (pctx, pctxops))) =>
  EX sh:share, 
  !!(readable_share sh /\ is_pointer_or_null d) &&
  data_at sh (Tstruct _env_md_ctx_st noattr) (d,(mddata,(pctx, pctxops))) p
  end.

Lemma EVP_MD_CTX_NNnode_isptr vals p:
  EVP_MD_CTX_NNnode vals p |-- !!(isptr p).
Proof.
  unfold EVP_MD_CTX_NNnode. destruct vals as [d [mdd [pc pcops]]]. normalize.
  rewrite data_at_isptr. entailer!.
Qed.
Lemma EVP_MD_CTX_NNnode_isptr' vals p:
  EVP_MD_CTX_NNnode vals p  = (!!(isptr p) &&  EVP_MD_CTX_NNnode vals p).
Proof.
  apply pred_ext; [ entailer; apply EVP_MD_CTX_NNnode_isptr | entailer!].
Qed.

(*a possibly null node*)
Definition EVP_MD_CTX_node (vals:val*(val*(val*val))) (p:val):mpred :=
 (!!(p = nullval) && emp) || EVP_MD_CTX_NNnode vals p.

(*According to digest.h, EVP_MD_CTX_md may be invoked even if no digest has not been set, 
  returning null in this case. The other 3 functions are specified to crash in such a 
  situation - we hence strengthen the precondition to rule out these situations*)
Definition EVP_MD_CTX_md_SPEC := DECLARE _EVP_MD_CTX_md
  WITH ctx:val, d:val, x:val * (val * val)
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP ()
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_node (d, x) ctx)
  POST [ tptr (Tstruct _env_md_st noattr) ]
       PROP ()
       LOCAL (temp ret_temp (if Val.eq ctx nullval then nullval else d))
       SEP (EVP_MD_CTX_node (d, x) ctx).

Definition EVP_MD_CTX_size_SPEC := DECLARE _EVP_MD_CTX_size
  WITH ctx:val, r:EVP_MD_record, d:val, x:val * (val * val)
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP ()
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_NNnode (d, x) ctx;  EVP_MD_rep r d)
  POST [ tptr (Tstruct _env_md_st noattr) ]
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr (EVP_MD_rec_md_size r))))
       SEP (EVP_MD_CTX_NNnode (d, x) ctx;  EVP_MD_rep r d).

Definition EVP_MD_CTX_block_size_SPEC := DECLARE _EVP_MD_CTX_block_size
  WITH ctx:val, r:EVP_MD_record, d:val, x:val * (val * val)
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP ()
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_NNnode (d, x) ctx;  EVP_MD_rep r d)
  POST [ tptr (Tstruct _env_md_st noattr) ]
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr (EVP_MD_rec_block_size r))))
       SEP (EVP_MD_CTX_NNnode (d, x) ctx;  EVP_MD_rep r d).

Definition EVP_MD_CTX_type_SPEC := DECLARE _EVP_MD_CTX_type
  WITH ctx:val, r:EVP_MD_record, d:val, x:val * (val * val)
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP ()
      LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_NNnode (d, x) ctx;  EVP_MD_rep r d)
  POST [ tptr (Tstruct _env_md_st noattr) ]
       PROP ()
       LOCAL (temp ret_temp (Vint (Int.repr (NID_of_DigestNID (EVP_MD_rec_type r)))))
       SEP (EVP_MD_CTX_NNnode (d, x) ctx;  EVP_MD_rep r d).

Definition Gprog_DigAccessOps : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [EVP_MD_block_size_SPEC; EVP_MD_type_SPEC; EVP_MD_size_SPEC  (*called*);
   EVP_MD_CTX_md_SPEC; EVP_MD_CTX_size_SPEC; EVP_MD_CTX_block_size_SPEC; EVP_MD_CTX_type_SPEC].

Lemma body_EVP_MD_CTX_block_size: semax_body Vprog Gprog_DigAccessOps f_EVP_MD_CTX_block_size EVP_MD_CTX_block_size_SPEC.
Proof.
  start_function. 
  rewrite  EVP_MD_CTX_NNnode_isptr'; Intros. 
  forward_call (ctx, d, x).
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
  forward_call (ctx, d, x).
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
  forward_call (ctx, d, x).
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
      SEP (EVP_MD_CTX_NNnode (d, (mddata, (pctx, pctxops))) ctx)). 
+ clear H. apply orp_left; [ entailer! | unfold EVP_MD_CTX_NNnode; normalize; entailer!]. 
+ subst. forward.
+ forward. entailer!. destruct ctx; trivial; try contradiction.
  simpl in *; subst. elim H; trivial.
  apply orp_left; [ normalize | trivial].
+ unfold EVP_MD_CTX_NNnode. Intros sh. rename H into RSH.
  forward.
  rewrite data_at_isptr; normalize. 
  forward. rewrite if_false. 2: destruct ctx; try contradiction; discriminate.
  normalize. apply orp_right2. Exists sh. entailer!.
Qed.  

(*Continiue here
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
