Require Import floyd.proofauto.
Require Import floyd.library.
Require Import dig.digests.
Require Import dig.digest.

Lemma data_at__valid_pointer {cs : compspecs} sh t p:
  sepalg.nonidentity sh ->
  sizeof t > 0 ->
  @data_at_ cs sh t p |-- valid_pointer p.
Proof. intros. unfold data_at_, field_at_. apply field_at_valid_ptr0; simpl; trivial. Qed.

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

(*Qinxiang says: proving this needs more work in verificable, namely
  conversion between different base types (4 null byes = 1 null integer etc.
  Also, walking through the array then and to "spin off" values in the right chunks*)
Axiom convert: forall sh p, data_at sh (tarray tuchar 16)
  [Vint Int.zero; Vint Int.zero; Vint Int.zero;
  Vint Int.zero; Vint Int.zero; Vint Int.zero;
  Vint Int.zero; Vint Int.zero; Vint Int.zero;
  Vint Int.zero; Vint Int.zero; Vint Int.zero;
  Vint Int.zero; Vint Int.zero; Vint Int.zero;
  Vint Int.zero] p
|-- data_at sh (Tstruct _env_md_ctx_st noattr)
      (nullval, (nullval, (nullval, nullval))) p.

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
(*Definition OPENSSL_cleanse_SPEC := DECLARE _OPENSSL_cleanse
  WITH p: val, sh : share, n:Z, case: unit + unit
  PRE [ 1%positive OF tptr tvoid , 2%positive OF tuint]
      PROP(writable_share sh; 0 <= n <= Int.max_unsigned) 
      LOCAL (temp 1%positive p; temp 2%positive (Vint (Int.repr n)))
      SEP (match case with
             inl _ => memory_block sh n p
           | inr _ => !!(n=sizeof (Tstruct _env_md_ctx_st noattr)) 
                      && data_at_ sh (Tstruct _env_md_ctx_st noattr) p
           end)
  POST [ tvoid ]
    PROP () LOCAL () 
    SEP (match case with
           inl _ => data_at sh (tarray tuchar n) (list_repeat (Z.to_nat n) (Vint Int.zero)) p
         | inr _ => data_at sh (Tstruct _env_md_ctx_st noattr) (nullval, (nullval, (nullval, nullval))) p
         end).*)
Definition OPENSSL_cleanse_SPEC := DECLARE _OPENSSL_cleanse
  WITH p: val, sh : share, n:Z
  PRE [ 1%positive OF tptr tvoid , 2%positive OF tuint]
      PROP(writable_share sh; 0 <= n <= Int.max_unsigned) 
      LOCAL (temp 1%positive p; temp 2%positive (Vint (Int.repr n)))
      SEP (memory_block sh n p)
  POST [ tvoid ]
    PROP () LOCAL () 
    SEP (data_at sh (tarray tuchar n) (list_repeat (Z.to_nat n) (Vint Int.zero)) p).

Definition type_of_ctx (v:reptype (Tstruct _env_md_ctx_st noattr)) :=
  match v with
    (type, (mddata, pv)) => type
  end.
Definition mddata_of_ctx (v:reptype (Tstruct _env_md_ctx_st noattr)) :=
  match v with
    (type, (mddata, pv)) => mddata
  end.

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

Definition get_type (vals:reptype (Tstruct _env_md_st noattr)):=
  match vals with
    (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) => type
  end.
Definition get_mdsize (vals:reptype (Tstruct _env_md_st noattr)):=
  match vals with
    (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) => mds
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
Definition get_blsize (vals:reptype (Tstruct _env_md_st noattr)):=
  match vals with
    (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) => blsize
  end.
Definition get_ctxsize (vals:reptype (Tstruct _env_md_st noattr)):=
  match vals with
    (type, (mds, (flags, (ini, (upd, (fin, (blsize, ctxsize))))))) => ctxsize
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
      PROP (writable_share sh)
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
  rewrite EVP_MD_NNnode_isptr'; Intros.
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

Parameter preUpd :Z -> val -> mpred.
Parameter postUpd: list val -> Z -> val -> mpred.

Definition upd_spec:funspec :=
  WITH ctx: val, (*history: list Z, *) sh:share, 
       CTX: reptype (Tstruct _env_md_ctx_st noattr),
       data: val, dsh:share, Data: list val, sz:Z, len:int
  PRE [ 1%positive OF (tptr (Tstruct _env_md_ctx_st noattr)), 
        2%positive OF tptr tvoid, 3%positive OF tuint]
       PROP (readable_share sh; readable_share dsh)
       LOCAL (temp 1%positive ctx; temp 2%positive data; temp 3%positive (Vint len) )
       SEP (data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;        
            data_at dsh (tarray tuchar (Int.unsigned len)) Data data;
            preUpd sz (mddata_of_ctx CTX))
  POST [ tvoid ]
          PROP() LOCAL () 
          SEP(data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
              data_at dsh (tarray tuchar (Int.unsigned len)) Data data;
              postUpd Data sz (mddata_of_ctx CTX)).

Definition EVP_DigestUpdate_SPEC := DECLARE _EVP_DigestUpdate
  WITH ctx: val, (*history: list Z, *) sh:share, 
       CTX: reptype (Tstruct _env_md_ctx_st noattr),
       data: val, dsh:share, Data: list val, sz:Z, len:int, 
       tsh:share, vals:reptype (Tstruct _env_md_st noattr)
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), _data OF tptr tvoid,  _len OF tuint ]
      PROP (readable_share sh; readable_share dsh; readable_share tsh)
      LOCAL (temp _ctx ctx; temp _data data; temp _len (Vint len) )
      SEP (data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;        
            data_at dsh (tarray tuchar (Int.unsigned len)) Data data;
            preUpd sz (mddata_of_ctx CTX); 
            EVP_MD_NNnode tsh vals (type_of_ctx CTX);
            func_ptr' upd_spec (get_updptr vals))
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
              data_at dsh (tarray tuchar (Int.unsigned len)) Data data;
              postUpd Data sz (mddata_of_ctx CTX);
              EVP_MD_NNnode tsh vals (type_of_ctx CTX);
              func_ptr' upd_spec (get_updptr vals)).

Definition Gprog_DigestUpdate : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [].

Lemma body_DigestUpdate: semax_body Vprog Gprog_DigestUpdate f_EVP_DigestUpdate EVP_DigestUpdate_SPEC.
Proof. 
  start_function. unfold EVP_MD_NNnode; Intros.
  destruct CTX as [d [md [pv1 pv2]]]. simpl in *. forward.
  destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]].  
  simpl in *. forward. 
  forward_call (ctx, sh, (d, (md, (pv1, pv2))), 
                data, dsh, Data, sz, len).
  { simpl; cancel. }
  forward. unfold EVP_MD_NNnode; entailer!.
Qed.

Parameter preFin : share -> Z -> list val -> val -> mpred.

Definition postFin sh (n:Z) p: mpred :=
           !!(0 <= n) && data_at sh (tarray tuchar n) (list_repeat (Z.to_nat n) (Vint Int.zero)) p.
Lemma postFin_memory_block sh n p: postFin sh n p |-- memory_block sh n p.
Proof. unfold postFin; Intros. eapply derives_trans. apply data_at_memory_block.
  simpl. rewrite Z.mul_1_l, Z.max_r; trivial.
Qed.
 
Lemma postFin_pTN sh n md: postFin sh n md |-- !!(is_pointer_or_null md).
Proof. eapply derives_trans. apply postFin_memory_block. entailer!. Qed.


Parameter Finresult: list val -> val -> mpred.
Definition fin_spec:funspec :=
  WITH ctx: val, (*history: list Z, *) sh:share, 
       CTX: reptype (Tstruct _env_md_ctx_st noattr),
       out: val, osh:share, content: list val, dsh:share, sz:Z, len:Z
  PRE [ 1%positive OF tptr (Tstruct _env_md_ctx_st noattr),
        2%positive OF tptr tuchar]
       PROP (readable_share sh; writable_share osh; writable_share dsh)
       LOCAL (temp 1%positive ctx; temp 2%positive out)
       SEP (data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
            preFin dsh sz content (mddata_of_ctx CTX); 
            memory_block osh len out)
  POST [ tvoid ]
          PROP() LOCAL () 
          SEP(data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
              postFin dsh sz (mddata_of_ctx CTX);
              Finresult content out).

Definition EVP_DigestFinal_ex_SPEC := DECLARE _EVP_DigestFinal_ex
  WITH ctx: val, (*history: list Z, *) sh:share, 
       CTX: reptype (Tstruct _env_md_ctx_st noattr),
       out: val, osh:share, sz:val,
       tsh:share, vals:reptype (Tstruct _env_md_st noattr), 
       ctxsz: int, content:list val, dsh:share, mdsize:int
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr),
        _md_out OF tptr tuchar, _size OF tptr tuint]
      PROP (readable_share sh; writable_share osh; readable_share tsh; writable_share dsh;
            (*get_blsize vals = Vint blksz; *)
            get_ctxsize vals = Vint ctxsz;
            get_mdsize vals = Vint mdsize; 0 <= Int.unsigned ctxsz <= Int.max_unsigned)
      LOCAL (temp _ctx ctx; temp _md_out out; temp _size sz )
      SEP (data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
            preFin dsh (Int.unsigned ctxsz) content (mddata_of_ctx CTX); 
            EVP_MD_NNnode tsh vals (type_of_ctx CTX);
            func_ptr' fin_spec (get_finptr vals); 
            if Val.eq sz nullval then emp else data_at_ Tsh tuint sz;
            memory_block osh (Int.unsigned mdsize) out)
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
              postFin dsh (Int.unsigned ctxsz) (mddata_of_ctx CTX);
              EVP_MD_NNnode tsh vals (type_of_ctx CTX);
              func_ptr' fin_spec (get_finptr vals);
              if Val.eq sz nullval then emp else data_at Tsh tuint (Vint mdsize) sz;
              Finresult content out).

Definition Gprog_DigestFinal_ex : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [OPENSSL_cleanse_SPEC].

Lemma body_DigestFinal_ex: semax_body Vprog Gprog_DigestFinal_ex f_EVP_DigestFinal_ex EVP_DigestFinal_ex_SPEC.
Proof. 
  start_function. unfold EVP_MD_NNnode; Intros. rename H into CTXSZ1.
  rename H0 into MDSZ. rename H1 into CTXSZ2. 
  destruct CTX as [d [md [pv1 pv2]]]; simpl in *. forward.
  destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
  forward. 
  forward_call (ctx, sh, (d, (md, (pv1, pv2))), 
                out, osh, content, dsh, Int.unsigned ctxsz, Int.unsigned mdsize).
  { simpl; cancel. }
  simpl. replace_SEP 1 (!!(is_pointer_or_null md)&&postFin dsh (Int.unsigned ctxsz) md).
  { entailer. apply postFin_pTN. } 
  Intros. 
  forward_if (PROP ( )
   LOCAL (temp _ctx ctx; temp _md_out out; temp _size sz)
   SEP (data_at sh (Tstruct _env_md_ctx_st noattr) (d, (md, (pv1, pv2))) ctx;
        postFin dsh (Int.unsigned ctxsz) md;
        Finresult content out;
        if Val.eq sz nullval then emp else data_at Tsh tuint (Vint mdsize) sz;
        data_at tsh (Tstruct _env_md_st noattr)
          (type, (Vint mdsize, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d;
        func_ptr' fin_spec fin)). 
   { clear H.
     apply denote_tc_test_eq_split; [ apply sepcon_valid_pointer2 | apply valid_pointer_null].
     destruct (Val.eq sz nullval); [subst; apply valid_pointer_null | apply data_at__valid_pointer; intuition ]. }
   { forward. forward. rewrite if_false; trivial.
     forward. rewrite if_false; trivial. entailer!. }
   { subst. forward. entailer!. }
   forward. forward. forward. simpl.
   replace_SEP 1 (memory_block dsh (Int.unsigned ctxsz) md).
   { entailer!. apply postFin_memory_block. } 
   forward_call (md, dsh, Int.unsigned ctxsz).
   { simpl. rewrite Int.repr_unsigned.
     rewrite eval_cast_neutral_is_pointer_or_null; trivial; simpl. entailer!. }
   forward. unfold EVP_MD_NNnode, postFin. entailer!.
Qed.

Definition EVP_DigestFinal_SPEC := DECLARE _EVP_DigestFinal
  WITH ctx: val, (*history: list Z, *) sh:share, 
       CTX: reptype (Tstruct _env_md_ctx_st noattr),
       out: val, osh:share, sz:val,
       tsh:share, vals:reptype (Tstruct _env_md_st noattr), 
       ctxsz: int, content:list val, mdsize:int
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr),
        _md OF tptr tuchar, _size OF tptr tuint]
      PROP (writable_share sh; writable_share osh; readable_share tsh; 
            get_ctxsize vals = Vint ctxsz;
            0 < Int.unsigned ctxsz <= Int.max_unsigned;
            snd(snd(snd CTX))=nullval; (*pv2*)
            (*get_blsize vals = Vint blksz; *)
            get_mdsize vals = Vint mdsize)
      LOCAL (temp _ctx ctx; temp _md out; temp _size sz )
      SEP (data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
            preFin Tsh (Int.unsigned ctxsz) content (mddata_of_ctx CTX); 
            EVP_MD_NNnode tsh vals (type_of_ctx CTX);
            func_ptr' fin_spec (get_finptr vals); 
            if Val.eq sz nullval then emp else data_at_ Tsh tuint sz;
            memory_block osh (Int.unsigned mdsize) out)
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (data_at_ sh (Tstruct _env_md_ctx_st noattr) ctx;
              EVP_MD_NNnode tsh vals (type_of_ctx CTX);
              func_ptr' fin_spec (get_finptr vals);
              if Val.eq sz nullval then emp else data_at Tsh tuint (Vint mdsize) sz;
              Finresult content out).

Definition Gprog_DigestFinal : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [EVP_DigestFinal_ex_SPEC; EVP_MD_CTX_cleanup_SPEC4].

Lemma body_DigestFinal: semax_body Vprog Gprog_DigestFinal f_EVP_DigestFinal EVP_DigestFinal_SPEC.
Proof. 
  start_function. rename H into CTXSZ1. rename H0 into CTXSZ2.
  rename H1 into PV2. rename H2 into MDSZ.
  assert (CTXSZ3: Int.eq ctxsz Int.zero = false).
  { destruct (Int.eq_dec ctxsz Int.zero); subst.
    unfold Int.zero in CTXSZ2; rewrite Int.unsigned_repr in CTXSZ2; omega.
    rewrite Int.eq_false; trivial. }
  forward_call (ctx, sh, CTX, out, osh, sz, tsh, vals, ctxsz, content, Tsh, mdsize).
  { intuition. }
  destruct CTX as [d [mdd [pv1 pv2]]]; simpl in *; subst.
  rewrite EVP_MD_NNnode_isptr'; Intros; simpl.
  assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] ctx) as FC by entailer!.
  (*replace_SEP 1 (!!(is_pointer_or_null mdd)&&postFin dsh (Int.unsigned ctxsz) mdd).
  { entailer. apply postFin_pTN. } *)
  replace_SEP 1 (memory_block Tsh (Int.unsigned ctxsz) mdd).
  { entailer. apply postFin_memory_block. }
  forward_call (ctx, sh, mdd, pv1, 
       @inr unit (share * val * reptype (Tstruct _env_md_st noattr)) (tsh,d,vals)). 
  { Exists ctxsz; entailer!. rewrite ! sepcon_assoc.
    apply sepcon_derives; [ apply orp_right2; trivial | cancel]. }
  forward. cancel. rewrite 2 data_at__memory_block; simpl. entailer!.
Qed.

Parameter preInit postInit: Z -> val -> mpred.
Parameter preInit_fresh: forall ctxsz m, 
  memory_block Tsh (Int.unsigned ctxsz) m |--preInit (Int.unsigned ctxsz) m.

Definition ini_spec:funspec :=
  WITH ctx: val, (*history: list Z, *) sh:share, 
       CTX: reptype (Tstruct _env_md_ctx_st noattr),
       dsh: share, dvals: reptype (Tstruct _env_md_st noattr), ctxsz:int
  PRE [ 1%positive OF tptr (Tstruct _env_md_ctx_st noattr)]
          PROP (writable_share sh; readable_share dsh; get_ctxsize dvals = Vint ctxsz)
          LOCAL (temp 1%positive ctx)
          SEP (data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
               preInit (Int.unsigned ctxsz) (mddata_of_ctx CTX);
               data_at dsh (Tstruct _env_md_st noattr) dvals (type_of_ctx CTX))
  POST [ tvoid ]
          PROP() LOCAL () 
          SEP(data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
              postInit (Int.unsigned ctxsz) (mddata_of_ctx CTX);
              data_at dsh (Tstruct _env_md_st noattr) dvals (type_of_ctx CTX)).

Inductive digestInitEx_cases :=
  DT_eq: forall (sh:share) (md pv2:val) (tsh:share)
                (tvals:reptype (Tstruct _env_md_st noattr)) (ctxsz':int), digestInitEx_cases
| D_null: forall (sh:share) (md pv2:val) (tsh:share)
                 (tvals:reptype (Tstruct _env_md_st noattr)) (ctxsz':int), digestInitEx_cases
| DT_neq: forall (sh:share) (d md pv2:val) (dvals:reptype (Tstruct _env_md_st noattr))
                 (ctxsz : int) (dsh:share) (tsh:share)
                 (tvals:reptype (Tstruct _env_md_st noattr)) (ctxsz':int), digestInitEx_cases.

Definition digestInitEx_pre (c: digestInitEx_cases) (ctx t:val):mpred  :=
match c with
  DT_eq sh md pv2 tsh tvals ctxsz'=> 
       !!(get_ctxsize tvals = Vint ctxsz' /\
                      ((*Int.unsigned ctxsz' <= 0 \/ *)4 <= Int.unsigned ctxsz' <= Int.max_unsigned)
                      /\ is_pointer_or_null (get_iniptr tvals) /\ writable_share sh)
                   && EVP_MD_CTX_NNnode sh (t, (md, (nullval, pv2))) ctx *
                      preInit (Int.unsigned ctxsz') md * EVP_MD_NNnode tsh tvals t *
                      func_ptr' ini_spec (get_iniptr tvals)
| D_null sh md pv2 tsh tvals ctxsz'=>
      !!(get_ctxsize tvals = Vint ctxsz' /\
                      ((*Int.unsigned ctxsz' <= 0 \/ *)4 <= Int.unsigned ctxsz' <= Int.max_unsigned)
                      /\ is_pointer_or_null (get_iniptr tvals) /\ writable_share sh)
                   && EVP_MD_CTX_NNnode sh (nullval, (md, (nullval, pv2))) ctx *
                      EVP_MD_NNnode tsh tvals t *
                      func_ptr' ini_spec (get_iniptr tvals)
| DT_neq sh d md pv2 dvals ctxsz dsh tsh tvals ctxsz'=> 
      !!(get_ctxsize tvals = Vint ctxsz' /\
                      ((*Int.unsigned ctxsz' <= 0 \/ *)4 <= Int.unsigned ctxsz' <= Int.max_unsigned)
                      /\ is_pointer_or_null (get_iniptr tvals) /\ d<>t /\ writable_share sh
                      /\ get_ctxsize dvals = Vint ctxsz /\  Int.ltu Int.zero ctxsz = true)
      && (EVP_MD_CTX_NNnode sh (d, (md, (nullval, pv2))) ctx *
          EVP_MD_NNnode dsh dvals d * EVP_MD_NNnode tsh tvals t *
          func_ptr' ini_spec (get_iniptr tvals) *
          (!!(md=nullval)&&emp || memory_block Tsh (Int.unsigned ctxsz) md))
end.

Definition digestInitEx_post (c: digestInitEx_cases) (ctx t rv:val):mpred  :=
match c with
  DT_eq sh md pv2 tsh tvals  ctxsz' => !!(rv = Vint Int.one) 
                     && data_at sh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, pv2))) ctx
                     * postInit (Int.unsigned ctxsz') md * EVP_MD_NNnode tsh tvals t * func_ptr' ini_spec (get_iniptr tvals)
| D_null sh md pv2 tsh tvals ctxsz' => (!!(rv= nullval) && 
             data_at sh (Tstruct _env_md_ctx_st noattr) (t, (nullval, (nullval, pv2))) ctx 
             * EVP_MD_NNnode tsh tvals t * func_ptr' ini_spec (get_iniptr tvals))
         || EX m :_, (!!(rv= Vint Int.one /\ malloc_compatible (Int.unsigned ctxsz') m) 
             && data_at sh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, pv2))) ctx * 
                postInit (Int.unsigned ctxsz') m * EVP_MD_NNnode tsh tvals t*  func_ptr' ini_spec (get_iniptr tvals))
| DT_neq sh d md pv2 dvals ctxsz dsh tsh tvals  ctxsz'=> 
     (!!(rv= Vint (Int.repr 0)) 
      && data_at dsh (Tstruct _env_md_st noattr) dvals d 
         * EVP_MD_NNnode tsh tvals t * func_ptr' ini_spec (get_iniptr tvals) *
         data_at sh (Tstruct _env_md_ctx_st noattr) (t, (nullval, (nullval, pv2))) ctx)
  || (EX m:_, !!(rv= Vint Int.one /\ malloc_compatible (Int.unsigned ctxsz') m)
       && data_at sh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, pv2))) ctx * 
          postInit (Int.unsigned ctxsz') m * data_at dsh (Tstruct _env_md_st noattr) dvals d * 
          EVP_MD_NNnode tsh tvals t * func_ptr' ini_spec (get_iniptr tvals))
end.

Definition EVP_DigestInit_ex_SPEC := DECLARE _EVP_DigestInit_ex
  WITH ep: val, ctx:val, t:val, e:val, (*tsh:share,*) c: digestInitEx_cases(*,
       tvals:reptype (Tstruct _env_md_st noattr)*)
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr),
        _engine OF tptr (Tstruct _engine_st noattr) ]
      PROP ()
      LOCAL (gvar ___stringlit_1 ep; temp _type t; temp _ctx ctx; temp _engine e)
      SEP (ERR ep; 
           digestInitEx_pre c ctx t)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERR ep; 
            digestInitEx_post c ctx t rv).

Definition Gprog_DigestInit_ex : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [EVP_DigestInit_ex_SPEC; OPENSSL_PUT_ERROR_SPEC; OPENSSL_free_SPEC; OPENSSL_malloc_SPEC].

Definition XPred ctxsz' sh t pv2 ctx: mpred :=
 (EX m : val,
          !! (0 < Int.unsigned ctxsz' /\ malloc_compatible (Int.unsigned ctxsz') m)
          && data_at sh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, pv2))) ctx *
             memory_block Tsh (Int.unsigned ctxsz') m).

Lemma body_DigestInit_ex: semax_body Vprog Gprog_DigestInit_ex f_EVP_DigestInit_ex EVP_DigestInit_ex_SPEC.
Proof. 
  start_function. 
  destruct c; normalize.
+ (* Case DT_eq*) 
  simpl; Intros; subst.
  rename H into CTXSZ1'. 
  rename H0 into CTXSZ2'. (*destruct H as [ctxsz' [CTXSZ1' CTXSZ2']] .*)
  rename H1 into Ini'. (*destruct H0 as [ini'' [ getini' Ini']].*)
  rename H2 into SH.
  rewrite EVP_MD_NNnode_isptr'; unfold EVP_MD_NNnode; Intros. rename H into TSH.
  freeze [4] FUNCS. 
  rewrite data_at_isptr with (p:=ctx); Intros.
  forward.
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _type t;
           temp _ctx ctx; temp _engine e)
    SEP (ERR ep; FRZL FUNCS; preInit (Int.unsigned ctxsz') md;
         data_at sh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, pv2))) ctx;
         data_at tsh (Tstruct _env_md_st noattr) tvals t)).
  - apply ptr_comp_Cne_t in H; congruence.
  - forward. entailer!.
  - forward. thaw FUNCS. 
    destruct tvals as [type' [mds' [flags' [ini' [upd' [fin' [blsize' ctxsize'']]]]]]]. 
    simpl in type', mds', flags', ini', upd', fin', ctxsize'', blsize', CTXSZ1', CTXSZ2', Ini'; subst.
    simpl. forward. 
    forward_call (ctx, sh, (t, (md, (nullval, pv2))), tsh, 
                   (type', (mds', (flags', (ini', (upd', (fin', (blsize', Vint ctxsz'))))))), ctxsz').
    { simpl. cancel. } 
    simpl; forward. Exists (Vint (Int.one)); unfold EVP_MD_NNnode; entailer!.

+ (* Case D_null*)
  simpl; Intros; subst. 
  rename H into CTXSZ1'. 
  rename H0 into CTXSZ2'. (*destruct H as [ctxsz' [CTXSZ1' CTXSZ2']] .*)
  rename H1 into Ini'. (*destruct H0 as [ini'' [ getini' Ini']].*)
  rename H2 into SH. 
  rewrite EVP_MD_NNnode_isptr'; unfold EVP_MD_NNnode; Intros. rename H into TSH. 
  freeze [3] FUNCS.
  rewrite data_at_isptr with (p:=ctx); Intros.
  forward.
  forward_if (
     PROP ( )
     LOCAL (gvar ___stringlit_1 ep;
            temp _type t; temp _ctx ctx; temp _engine e)
     SEP (ERR ep; FRZL FUNCS; 
          data_at tsh (Tstruct _env_md_st noattr) tvals t;
          (*( !!(Int.unsigned ctxsz' <= 0)
             && data_at sh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, pv2))) ctx)
           || *)(!!(0 < Int.unsigned ctxsz')
               && EX m:_, !!(malloc_compatible (Int.unsigned ctxsz') m) &&
                  data_at sh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, pv2))) ctx *
                  memory_block Tsh (Int.unsigned ctxsz') m))).
  2: solve [ apply ptr_comp_Cne_f in H; simpl; trivial; subst; try contradiction; destruct t; try contradiction; trivial]. 
  - clear H.
    forward.
    forward_if (PROP ( )
      LOCAL (temp _t'1 nullval; gvar ___stringlit_1 ep; temp _type t; 
             temp _ctx ctx; temp _engine e)
      SEP (ERR ep; FRZL FUNCS; 
           data_at sh (Tstruct _env_md_ctx_st noattr) (nullval, (md, (nullval, pv2))) ctx;
           data_at tsh (Tstruct _env_md_st noattr) tvals t));
     [ solve [contradiction] | solve [forward ; entailer!] | ].
    forward_if (
      PROP ( )
      LOCAL (gvar ___stringlit_1 ep;
             temp _type t; temp _ctx ctx; temp _engine e)
      SEP (ERR ep; FRZL FUNCS; 
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
      SEP (ERR ep; FRZL FUNCS; 
           data_at tsh (Tstruct _env_md_st noattr)
              (type', (mds', (flags', (ini', (upd', (fin', (blsize', Vint ctxsz'))))))) t;
           (*( !!(Int.unsigned ctxsz' <= 0)
             && data_at sh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, pv2))) ctx)
           || *)(!!(0 < Int.unsigned ctxsz')
               && EX m:_, !!(malloc_compatible (Int.unsigned ctxsz') m) &&
                  data_at sh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, pv2))) ctx *
                  memory_block Tsh (Int.unsigned ctxsz') m))).
    { (*destruct CTXSZ2'; [ omega | clear H].*)clear H. forward.
      forward_call (Int.unsigned ctxsz'). rewrite Int.repr_unsigned; entailer!. 
      Intros m. forward. forward. deadvars.
      apply semax_orp_SEPx; Intros; subst.
      + (*m==null*)
        rewrite eval_cast_neutral_is_pointer_or_null; simpl; trivial.
        forward_if (PROP (False) LOCAL () SEP ()).
        * clear H.
          forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                 ep, Vint (Int.repr 177)). 
          freeze [0;1;2;3] FRALL. forward.
          Exists nullval. thaw FRALL; thaw FUNCS. simpl. entailer!.
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
               ERR ep; FRZL FUNCS; 
               data_at sh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, pv2))) ctx;
               data_at tsh (Tstruct _env_md_st noattr)
                 (type', (mds', (flags', (ini', (upd', (fin', (blsize', Vint ctxsz'))))))) t)).
        * clear H.
          apply denote_tc_test_eq_split; [ apply sepcon_valid_pointer1 | apply valid_pointer_null].
          apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
          (*apply sepcon_valid_pointer1. *) apply memory_block_valid_ptr. intuition. omega.
        * subst m; contradiction.
        * clear H. forward. entailer!.
        * intros. unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
          old_go_lower. clear H. destruct ek; simpl; normalize. entailer!. 
          (*apply orp_right2. *) Exists m; entailer!. } 
    { omega. (*destruct CTXSZ2'; [ clear H | omega ]. clear H. forward. entailer!.
      apply orp_right1; trivial.*)  }
    intros. unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
    old_go_lower. clear H. destruct ek; simpl; normalize. Exists m; entailer!.
  - Intros m. clear H; rename H0 into M. 
    destruct tvals as [type' [mds' [flags' [ini' [upd' [fin' [blsize' ctxsize'']]]]]]]. 
    simpl in type', mds', flags', ini', upd', fin', ctxsize'', blsize', CTXSZ1', CTXSZ2', Ini'; subst; simpl.
    forward.
    forward. thaw FUNCS. simpl.
    replace_SEP 4 (preInit (Int.unsigned ctxsz') m). { entailer!. apply preInit_fresh. } 
    forward_call (ctx, sh, (t, (m, (nullval, pv2))), tsh, 
                   (type', (mds', (flags', (ini', (upd', (fin', (blsize', Vint ctxsz'))))))), ctxsz').
      { simpl. cancel. } 
    simpl; forward. Exists (Vint (Int.one)); unfold EVP_MD_NNnode; entailer!.
    apply orp_right2. Exists m. entailer!.
+ (*Case DT_neq*)
  simpl; Intros; subst.
  rename H into CTXSZ1'. 
  rename H0 into CTXSZ2'. (*destruct H as [ctxsz' [CTXSZ1' CTXSZ2']] .*)
  rename H1 into Ini'. (*destruct H0 as [ini'' [ getini' Ini']].*)
  rename H2 into DT.
  rename H3 into SH.
  rename H4 into CTXSZ1. rename H5 into CTXSZ2.
  rewrite EVP_MD_NNnode_isptr'; unfold EVP_MD_NNnode; Intros.
  rename H into DSH. rename H0 into TSH.
  freeze [4] FUNCS. 
  rewrite data_at_isptr with (p:=ctx); Intros.
  freeze [3] D. freeze [5] MD. 
  forward. thaw MD; thaw D. thaw FUNCS.
  destruct dvals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
  simpl in type, mds, flags,ini, upd, fin, ctxsize, blsize, CTXSZ1.
  destruct tvals as [type' [mds' [flags' [ini' [upd' [fin' [blsize' ctxsize'']]]]]]]. 
  simpl in type', mds', flags',ini', upd', fin', ctxsize'', blsize', CTXSZ1', CTXSZ2', Ini'; subst; simpl.
  freeze [4] CTX. freeze [1] MD. freeze [3] FUNCS. rewrite data_at_isptr with (p:=t); Intros.
  freeze [0;1;2;4] ALLFR. (* subst dvals tvals; simpl. *) simpl.
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep;
           temp _type t; temp _ctx ctx; temp _engine e)
    SEP (XPred ctxsz' sh t pv2 ctx;
         ERR ep; FRZL FUNCS;
         data_at tsh (Tstruct _env_md_st noattr) (type', (mds', (flags', (ini', (upd', (fin', (blsize', Vint ctxsz'))))))) t;
         data_at dsh (Tstruct _env_md_st noattr) (type, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz)))))))  d)).
  2: solve [ apply ptr_comp_Cne_f in H; trivial; try contradiction; destruct t; try contradiction; trivial].
  { clear H. thaw ALLFR.
    unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
    thaw FUNCS; thaw MD; thaw CTX. 
    freeze [0] FUNCS. freeze [4;5] DTFR. freeze [2] MD. simpl. forward.
    forward_if (
      PROP ( )
      LOCAL (temp _t'1 (Vint Int.one); gvar ___stringlit_1 ep; temp _type t; temp _ctx ctx; temp _engine e)
      SEP (FRZL DTFR; FRZL MD; ERR ep; FRZL FUNCS;
           data_at sh (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, pv2))) ctx)).
    { clear H. apply denote_tc_test_eq_split; 
          [apply sepcon_valid_pointer1 | apply valid_pointer_null].
      apply sepcon_valid_pointer1; apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
      clear MD; thaw DTFR. apply sepcon_valid_pointer1. entailer!. }
    { clear H. forward. unfold POSTCONDITION, abbreviate; clear POSTCONDITION; thaw MD; thaw DTFR.
      simpl. forward. forward.
      go_lower. normalize. unfold Int.zero in CTXSZ2. simpl; rewrite CTXSZ2. 
      apply andp_right; [ apply prop_right; repeat split; trivial | cancel ]. }
    { subst d; contradiction. }
    thaw MD.
    forward_if (
      PROP ( )
      LOCAL (gvar ___stringlit_1 ep; 
             temp _type t; temp _ctx ctx; temp _engine e)
      SEP (FRZL DTFR; ERR ep; FRZL FUNCS;
           data_at sh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, pv2))) ctx)).
    { clear H. forward. 
      (*free*) forward_call (md, Int.unsigned ctxsz).
      forward. entailer!. }
    { inv H. }
    simpl. forward. simpl. rewrite sem_cast_neutral_ptr; simpl; trivial.
    thaw DTFR. freeze [0; 2;3] FR3. 
    forward. thaw FR3. freeze [0] FR_D.
    forward_if (
     PROP ( )
     LOCAL (gvar ___stringlit_1 ep;
            temp _type t; temp _ctx ctx; temp _engine e)
     SEP (FRZL FR_D; ERR ep; FRZL FUNCS; data_at tsh (Tstruct _env_md_st noattr)
     (type',
     (mds',
     (flags', (ini', (upd', (fin', (blsize', Vint ctxsz'))))))) t;
          (!!(0 < Int.unsigned ctxsz') 
           && (EX m:val, !!(malloc_compatible (Int.unsigned ctxsz') m) &&
                 data_at sh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, pv2))) ctx *
                 memory_block Tsh (Int.unsigned ctxsz') m)))).
     + (*0 < Int.unsigned ctxsz'*)
       clear H. 
       forward. 
       forward_call (Int.unsigned ctxsz').
       { rewrite Int.repr_unsigned; entailer!. }
       Intros m. freeze [4] FR_T.
       forward. forward. simpl.
       focus_SEP 1. apply semax_orp_SEPx; Intros; subst.
       { (*m==null*)
         forward_if (PROP (False) LOCAL () SEP ()).
         *  clear H.
            forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                ep, Vint (Int.repr 177)). 
            simpl. freeze [0;1;2;3;4] FRALL. 
            forward; Exists nullval; unfold EVP_MD_NNnode; thaw FRALL; entailer!. 
            apply orp_right1. apply andp_right; [ entailer! | thaw FR_T; thaw FR_D; thaw FUNCS; cancel]. 
         * inv H. 
         * intros. unfold overridePost. old_go_lower. clear H.
             destruct (EqDec_exitkind ek EK_normal). entailer!. cancel. }
       { (*m <> null*)
         rename H into M. rewrite memory_block_isptr; Intros.
         freeze [1;2;3;4;5] FR3. 
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
           (*apply orp_right1. *) Exists (eval_id _t'7 rho). entailer!. } 
     + (*Case 0 >= Int.unsigned ctxsz' *)
       omega. 
     + intros. unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
           old_go_lower. clear H.
           destruct ek; simpl; normalize. entailer!.
           thaw FR_D. thaw FUNCS; cancel. unfold XPred. Exists m. entailer!. } 
  clear ALLFR. thaw FUNCS. clear CTX MD. unfold XPred.
  (*apply semax_orp_SEPx. 
  - *)
  Intros m. clear H; rename H0 into M.
    freeze [1;2;3;5] FR5. simpl. forward. forward. thaw FR5. freeze [1;3] REST1.
      replace_SEP 1 (preInit (Int.unsigned ctxsz') m). { entailer!; apply preInit_fresh. } 
      forward_call (ctx, sh, (t, (m, (nullval, pv2))), tsh, 
                   (type', (mds', (flags', (ini', (upd', (fin', (blsize', Vint ctxsz'))))))), ctxsz').
      { simpl. cancel. } 
      simpl; forward. Exists (Vint (Int.one)); unfold EVP_MD_NNnode; entailer!.
      thaw REST1. cancel. apply orp_right2. Exists m. normalize.
      apply andp_right; [ apply prop_right; repeat split; trivial | cancel]. 
Time Qed.

Definition EVP_DigestInit_SPEC := DECLARE _EVP_DigestInit
  WITH ep: val, ctx:val, t:val, sh:share, tsh:share, 
       tvals:reptype (Tstruct _env_md_st noattr), ctxsz':int
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr) ]
      PROP (get_ctxsize tvals = Vint ctxsz';
            4 <= Int.unsigned ctxsz' <= Int.max_unsigned;
            is_pointer_or_null (get_iniptr tvals); writable_share sh)
      LOCAL (gvar ___stringlit_1 ep; temp _type t; temp _ctx ctx)
      SEP (ERR ep; func_ptr' ini_spec (get_iniptr tvals);
           data_at_ sh (Tstruct _env_md_ctx_st noattr) ctx;
           EVP_MD_NNnode tsh tvals t )
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERR ep; func_ptr' ini_spec (get_iniptr tvals); EVP_MD_NNnode tsh tvals t;
            ( !!(rv=nullval) 
               && data_at sh (Tstruct _env_md_ctx_st noattr)(t, (nullval, (nullval, nullval))) ctx)
         || ( EX m:val,
              !!(rv=Vint Int.one /\ malloc_compatible (Int.unsigned ctxsz') m) 
               && postInit (Int.unsigned ctxsz') m * 
                  data_at sh (Tstruct _env_md_ctx_st noattr)(t, (m, (nullval, nullval))) ctx)).

Definition Gprog_DigestInit : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [EVP_DigestInit_ex_SPEC; EVP_MD_CTX_init_SPEC].


Lemma body_DigestInit: semax_body Vprog Gprog_DigestInit f_EVP_DigestInit EVP_DigestInit_SPEC.
Proof. 
  start_function.
  assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] ctx) as FC by entailer!.
  forward_call (ctx, sh, sizeof (Tstruct _env_md_ctx_st noattr)); simpl. 
  replace_SEP 0 (data_at sh (Tstruct _env_md_ctx_st noattr) (nullval, (nullval, (nullval, nullval))) ctx).
    entailer. apply convert.
  forward_call (ep, ctx, t, nullval, D_null sh nullval nullval tsh tvals ctxsz').
  { simpl; entailer!. }
  Intros rv. simpl. forward. entailer!. Exists (Vint rv). entailer!.
  apply orp_left. 
  - Intros. cancel. apply orp_right1; entailer!.
  - Intros m. cancel. apply orp_right2; entailer!.
    Exists m; entailer!.
Qed.

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
  { (*holds because of FCout*) entailer. apply convert. }
  (*unfold data_at_, field_at_. simpl. unfold default_val.x simpl. *)
  forward_call (ep, octx, ictx, inDataNull ish d nullval pv2 dsh vals osh nullval nullval nullval).
  { simpl. destruct H1 as [ctxsz [H1a H1b]]. entailer!. simpl. Exists ctxsz. entailer!. }
  Intros v. forward. unfold POST3. 
  destruct vals as [type [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
  simpl in type, mds, flags,ini, upd, fin, ctxsize, blsize.
  destruct (Val.eq nullval nullval); [simpl | solve [ congruence ]].
  Intros ctxsz. Exists (Vint v); entailer!. cancel.
+ replace_SEP 3 (data_at osh (Tstruct _env_md_ctx_st noattr)
      (nullval, (nullval, (nullval, nullval))) octx).
  { (*holds because of FCout*) entailer. apply convert. }
  forward_call (ep, octx, ictx, 
                outDigest_Null ish d md nullval pv2 dsh vals osh nullval nullval imdsh idata ctxsz).
  { simpl. entailer!. } 
  Intros v. forward. Exists (Vint v); entailer!. 
Qed.

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


Existing Instance NullExtension.Espec.

Lemma all_funcs_correct:
  semax_func Vprog Gprog [](*(prog_funct prog)*) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
eapply semax_func_cons.
semax_func_cons body_EVP_MD_type. apply semax_func_cons_malloc_aux.
semax_func_cons body_free.
semax_func_cons body_exit.


Definition EVP_MD_CTX_rep (p:val):mpred :=
  EX sh:_, 
  !!readable_share sh &&
  data_at sh sh (Tstruct _env_md_ctx_st noattr)
*)