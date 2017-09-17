Require Import floyd.proofauto.
Require Import floyd.library.
Require Import dig.digests.
Require Import dig.digest.

Require Import List.  Import ListNotations.

Lemma ptr_comp_Ceq_t p q (P: is_pointer_or_null p) (Q: is_pointer_or_null q): 
      typed_true tint (force_val (sem_cmp_pp Ceq p q)) <-> (p=q).
Proof.
  destruct p; destruct q; try contradiction; simpl in *; subst;
  unfold typed_true, sem_cmp_pp; simpl; split; intros; trivial; try solve [inv H]; try discriminate.
+ destruct (eq_block b b0); subst; simpl; trivial; [| inv H].
  destruct (Int.eq_dec i i0); subst; simpl in *; trivial.
  rewrite Int.eq_false in H; trivial; inv H.
+ inv H; simpl. rewrite if_true, Int.eq_true; trivial.
Qed.

Lemma ptr_comp_Ceq_t' {T} p q 
      (H: typed_true tint (force_val (sem_cmp_pp Ceq p q)))
       (a b:T) (P: is_pointer_or_null p)
               (Q: is_pointer_or_null q):
      (if Val.eq p q then a else b) = a.
Proof. apply ptr_comp_Ceq_t in H; trivial.
  rewrite if_true; trivial.
Qed.

Lemma ptr_comp_Ceq_f p q (P: is_pointer_or_null p) (Q: is_pointer_or_null q): 
      typed_false tint (force_val (sem_cmp_pp Ceq p q)) <-> ~(p=q).
Proof.
  destruct p; destruct q; try contradiction; simpl in *; subst;
  unfold typed_false, sem_cmp_pp; simpl; split; intros; trivial; try solve [inv H]; try congruence. 
+ intros N; inv N. rewrite if_true, Int.eq_true in H; trivial; inv H.
+ destruct (eq_block b b0); subst; simpl; trivial.
  rewrite Int.eq_false; simpl; trivial. 
  intros N; subst; congruence. 
Qed.

Lemma ptr_comp_Ceq_f' {T} p q 
      (H: typed_false tint (force_val (sem_cmp_pp Ceq p q)))
       (a b:T) (P: is_pointer_or_null p)
               (Q: is_pointer_or_null q):
      (if Val.eq p q then a else b) = b.
Proof. apply ptr_comp_Ceq_f in H; trivial.
  rewrite if_false; trivial.
Qed.

Lemma ptr_comp_Cne_t p q (P: is_pointer_or_null p) (Q: is_pointer_or_null q): 
      typed_true tint (force_val (sem_cmp_pp Cne p q)) <-> ~(p=q).
Proof.
  destruct p; destruct q; try contradiction; simpl in *; subst;
  unfold typed_true, sem_cmp_pp; simpl; split; intros; trivial; try solve [inv H]; try discriminate.
+ elim H; trivial.
+ intros N; inv N. rewrite Int.eq_true in H; simpl in H. destruct (eq_block b0 b0); [subst; inv H | contradiction].
+ destruct (eq_block b b0); subst; simpl; trivial.
  destruct (Int.eq_dec i i0); subst; simpl; [congruence | rewrite Int.eq_false; trivial].
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
Record REPTYPE:Type := { REPTYPE_t: type; REPTYPE_v: reptype REPTYPE_t}.
Definition OPENSSL_memcpy_STRONGSPEC := DECLARE _OPENSSL_memcpy
   WITH sh : share*share, p: val, q: val, n:Z, x:REPTYPE
   PRE [ 1%positive OF tptr tvoid, 2%positive OF tptr tvoid, 3%positive OF tuint ]
       PROP (readable_share (fst sh); writable_share (snd sh); 
             0 <= n <= Int.max_unsigned; n=sizeof (REPTYPE_t x))
       LOCAL (temp 1%positive p; temp 2%positive q; temp 3%positive (Vint (Int.repr n)))
       SEP (data_at (fst sh) (REPTYPE_t x) (REPTYPE_v x) q;
              memory_block (snd sh) n p)
    POST [ tptr tvoid ]
       PROP() LOCAL(temp ret_temp p)
       SEP(data_at (fst sh) (REPTYPE_t x) (REPTYPE_v x) q;
             data_at (snd sh) (REPTYPE_t x) (REPTYPE_v x) p).

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

Definition EVP_add_digest_SPEC := DECLARE _EVP_add_digest
  WITH v:val
  PRE [_digest OF tptr (Tstruct _env_md_st noattr)]
      PROP () LOCAL (temp _digest v) SEP ()
  POST [tint] PROP () LOCAL (temp ret_temp (Vint Int.one)) SEP ().

Definition Gprog_EVP_add_digest : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [].

Lemma body_EVP_add_digest: semax_body Vprog Gprog_EVP_add_digest
                           f_EVP_add_digest EVP_add_digest_SPEC.
Proof. start_function. forward. Qed. 

Definition type_of_ctx (v:reptype (Tstruct _env_md_ctx_st noattr)) :=
  match v with
    (type, (mddata, pv)) => type
  end.
Definition mddata_of_ctx (v:reptype (Tstruct _env_md_ctx_st noattr)) :=
  match v with
    (type, (mddata, pv)) => mddata
  end.

(****** Used in the specs of the four Digest Operation Accessors. *******)
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

(*nonnull node*)
Definition EVP_MD_NNnode (sh:share) (vals:reptype (Tstruct _env_md_st noattr)) (p:val):mpred :=
  !!(readable_share sh) &&
  data_at sh (Tstruct _env_md_st noattr) vals p.

Lemma EVP_MD_NNnode_isptr sh vals p: EVP_MD_NNnode sh vals p |-- !!(isptr p).
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

Module Type EVP_MD_CTX_Protocol_TP.
Parameter MDCTXInitialized: val -> mpred.
Parameter MDCTXAllocated: val -> mpred.

(*Propose to Adam that this be eliminated - it's needed in 3 places*)
Parameter MDCTXInitializedDigestSet: val -> val -> mpred.

Axiom MDCTXAllocated_valid_ptr: forall p, MDCTXAllocated p |-- valid_pointer p.

Axiom MDCTXInitialized_MDCTXAllocated: forall p, MDCTXInitialized p|-- MDCTXAllocated p.

Axiom MDCTXInitializedDigestSet_MDCTXAllocated: forall t p, MDCTXInitializedDigestSet t p|-- MDCTXAllocated p.

Axiom MDCTXInitialized_valid_ptr: forall p, MDCTXInitialized p |-- valid_pointer p.

Axiom MDCTXInitializedDigestSet_valid_ptr: forall t p, MDCTXInitializedDigestSet t p |-- valid_pointer p.

Axiom MDCTXAllocated_isptr: forall p, MDCTXAllocated p |-- !! isptr p.

Axiom MDCTXInitialized_isptr: forall p, MDCTXInitialized p |-- !! isptr p.

Axiom MDCTXInitializedDigestSet_isptr: forall t p, MDCTXInitializedDigestSet t p |-- !! isptr p.

Axiom MDCTXAllocated_isptr': forall p, MDCTXAllocated p = (!!isptr p) && MDCTXAllocated p.

Axiom MDCTXInitialized_isptr': forall p, MDCTXInitialized p = (!! isptr p) && MDCTXInitialized p.

Axiom MDCTXInitializedDigestSet_isptr': forall t p, MDCTXInitializedDigestSet t p = (!! isptr p) && MDCTXInitializedDigestSet t p.

Definition EVP_MD_CTX_init_SPEC := DECLARE _EVP_MD_CTX_init
   WITH ctx:val
   PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr) ]
       PROP () LOCAL (temp _ctx ctx) SEP (MDCTXAllocated ctx)
   POST [ tvoid ]
       PROP () LOCAL () SEP (MDCTXInitialized ctx).

Definition EVP_MD_CTX_create_SPEC := DECLARE _EVP_MD_CTX_create
   WITH ctx:val
   PRE [ ]
       PROP () LOCAL ( ) SEP ()
   POST [ tptr (Tstruct _env_md_ctx_st noattr) ]
     EX ctx:val,
       PROP ()
       LOCAL (temp ret_temp ctx)
       SEP ((!!(ctx=nullval) && emp) || MDCTXInitialized ctx).

Definition Gprog_EVPMDCTX_1 : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [EVP_MD_CTX_create_SPEC; EVP_MD_CTX_init_SPEC; OPENSSL_memset_SPEC; OPENSSL_malloc_SPEC].

Axiom body_EVP_MD_CTX_init: semax_body Vprog Gprog_EVPMDCTX_1 f_EVP_MD_CTX_init EVP_MD_CTX_init_SPEC.

Axiom body_EVP_MD_CTX_create: semax_body Vprog Gprog_EVPMDCTX_1 f_EVP_MD_CTX_create EVP_MD_CTX_create_SPEC.

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

Axiom body_EVP_MD_CTX_block_size: semax_body Vprog Gprog_DigAccessOps f_EVP_MD_CTX_block_size EVP_MD_CTX_block_size_SPEC.
Axiom body_EVP_MD_CTX_type: semax_body Vprog Gprog_DigAccessOps f_EVP_MD_CTX_type EVP_MD_CTX_type_SPEC.
Axiom body_EVP_MD_CTX_size: semax_body Vprog Gprog_DigAccessOps f_EVP_MD_CTX_size EVP_MD_CTX_size_SPEC.
Axiom body_EVP_MD_CTX_md: semax_body Vprog Gprog_DigAccessOps f_EVP_MD_CTX_md EVP_MD_CTX_md_SPEC.

Definition Gprog_cleanup : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [OPENSSL_cleanse_SPEC; OPENSSL_free_SPEC; EVP_MD_CTX_init_SPEC].
(*
Parameter struct_of_nid: int -> option type.
Parameter DigestRep: forall (t:type) (v:reptype t) (data:list Z), Prop. (*should generalize s256_relate*)
Parameter DigestRepNil: forall t, DigestRep t (default_val t) [].
*)
Parameter MDCTXConfigured: forall (nid ctxsz:int) (d p:val), mpred.
Parameter MDCTXHashed: forall (nid ctxsz:int) (data:list Z) (d p:val), mpred.
Parameter MDCTXFinished: forall (nid ctxsz:int) (d p:val), mpred.

Axiom MDCTXConfigured_valid_ptr: forall nid ctxsz d p, MDCTXConfigured nid ctxsz d p |-- valid_pointer p.
Axiom MDCTXConfigured_isptr: forall nid ctxsz d p, MDCTXConfigured ctxsz nid d p |-- !! isptr p.
Axiom MDCTXConfigured_isptr': forall nid ctxsz d p, MDCTXConfigured nid ctxsz d p = (!!isptr p) && MDCTXConfigured nid ctxsz d p.

Axiom MDCTXHashed_valid_ptr: forall nid ctxsz data d p, MDCTXHashed nid ctxsz data d p |-- valid_pointer p.
Axiom MDCTXHashed_isptr: forall nid ctxsz data d p, MDCTXHashed nid ctxsz data d p |-- !! isptr p.
Axiom MDCTXHashed_isptr': forall nid ctxsz data d p,
      MDCTXHashed nid ctxsz data d p = (!!isptr p) && MDCTXHashed nid ctxsz data d p.

Axiom MDCTXHashed_MDCTXConfigured: forall nid ctxsz data d p, MDCTXHashed nid ctxsz data d p |-- MDCTXConfigured nid ctxsz d p.
Axiom MDCTXConfigured_MDCTXHashed: forall nid ctxsz d p, MDCTXConfigured nid ctxsz d p |-- MDCTXHashed nid ctxsz nil d p.

Axiom MDCTXFinished_valid_ptr: forall nid ctxsz d p, MDCTXFinished nid ctxsz d p |-- valid_pointer p.
Axiom MDCTXFinished_isptr: forall nid ctxsz d p, MDCTXFinished nid ctxsz d p |-- !! isptr p.
Axiom MDCTXFinished_isptr': forall nid ctxsz d p,
      MDCTXFinished nid ctxsz d p = (!!isptr p) && MDCTXFinished nid ctxsz d p.

Definition MDCTXHashedOrFinished nid ctxsz d p: mpred :=
  (EX data:_, MDCTXHashed nid ctxsz (map Int.unsigned data) d p) || MDCTXFinished nid ctxsz d p.

Axiom MDCTXHashedOrFinished_valid_ptr: forall nid ctxsz d p, MDCTXHashedOrFinished nid ctxsz d p |-- valid_pointer p.
Axiom MDCTXHashedOrFinished_isptr: forall nid ctxsz d p, MDCTXHashedOrFinished nid ctxsz d p |-- !!(isptr p).
Axiom MDCTXHashedOrFinished_isptr': forall nid ctxsz d p,
      MDCTXHashedOrFinished nid ctxsz d p = !!(isptr p) && MDCTXHashedOrFinished nid ctxsz d p.

(*Not exposed
Axiom MDCTXHashedOrFinished_MDCTXFinished: forall nid ctxsz d p,
      MDCTXHashedOrFinished nid ctxsz d p = MDCTXFinished nid ctxsz d p.

Lemma MDCTXFinished_MDCTXConfigured nid ctxsz d p:, MDCTXFinished nid ctxsz d p = MDCTXConfigured nid ctxsz d p.
Proof. unfold MDCTXFinished, MDCTXConfigured, postInit; apply pred_ext; Intros md t; Exists md t; entailer!. Qed.

Lemma MDCTXHashed_MDCTXFinished nid ctxsz data d p, MDCTXHashed nid ctxsz data d p |-- MDCTXFinished nid ctxsz d p.
Proof. unfold MDCTXFinished, MDCTXHashed; Intros md t v. Exists md t; entailer!. Qed.
*)

Inductive EVP_MD_CTX_cleanup_case :=
  ClInitialized: EVP_MD_CTX_cleanup_case
| ClInitializedDigestSet: forall (d:val) (dsh:share) (vals:reptype (Tstruct _env_md_st noattr)), EVP_MD_CTX_cleanup_case (*Talk with Adam to allow removal of this*)
| ClConfiguredOrFinished: forall (dsh:share) (vals:reptype (Tstruct _env_md_st noattr)) (d:val), EVP_MD_CTX_cleanup_case.

Definition EVP_MD_CTX_cleanup_pre (c:EVP_MD_CTX_cleanup_case) (ctx:val) : mpred :=
  match c with
   ClInitialized => MDCTXInitialized ctx
 | ClInitializedDigestSet t tsh vals => EX ctxsz:int, 
     !!(get_ctxsize vals = Vint ctxsz /\ Int.eq ctxsz Int.zero = false)
     && MDCTXInitializedDigestSet t ctx * EVP_MD_NNnode tsh vals t
 | ClConfiguredOrFinished dsh vals d => 
     EX nid:int, EX ctxsz:int, 
     !!(get_ctxsize vals = Vint ctxsz /\ get_type vals = Vint nid)
     && (MDCTXConfigured nid ctxsz d ctx || MDCTXFinished nid ctxsz d ctx) * EVP_MD_NNnode dsh vals d
end.

Definition EVP_MD_CTX_cleanup_post (c:EVP_MD_CTX_cleanup_case) (ctx:val) : mpred :=
  match c with
   ClInitialized => MDCTXInitialized ctx
 | ClInitializedDigestSet t tsh vals => MDCTXInitialized ctx * EVP_MD_NNnode tsh vals t
 | ClConfiguredOrFinished dsh vals d => MDCTXInitialized ctx * EVP_MD_NNnode dsh vals d
end.

Definition EVP_MD_CTX_cleanup_SPEC := DECLARE _EVP_MD_CTX_cleanup
  WITH ctx:val, c:EVP_MD_CTX_cleanup_case
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP () LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_cleanup_pre c ctx)
  POST [ tint ]
       PROP () LOCAL (temp ret_temp (Vint (Int.one)))
       SEP (EVP_MD_CTX_cleanup_post c ctx).

Axiom body_EVP_MD_CTX_cleanup: semax_body Vprog Gprog_cleanup f_EVP_MD_CTX_cleanup EVP_MD_CTX_cleanup_SPEC.

Parameter preInit: Z -> val -> mpred.
Parameter memblock_preInit: forall i m, memory_block Tsh i m |-- preInit i m.

Parameter postInit: forall (nid:int) (ctxsz:Z) (p:val), mpred.

Definition ini_spec:funspec :=
  WITH ctx: val, sh:share, 
       CTX: reptype (Tstruct _env_md_ctx_st noattr),
       dsh: share, dvals: reptype (Tstruct _env_md_st noattr), ctxsz:int, nid:int
  PRE [ 1%positive OF tptr (Tstruct _env_md_ctx_st noattr)]
          PROP (writable_share sh; readable_share dsh; get_ctxsize dvals = Vint ctxsz;
                get_type dvals = Vint nid)
          LOCAL (temp 1%positive ctx)
          SEP (data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
               preInit (Int.unsigned ctxsz) (mddata_of_ctx CTX);
               data_at dsh (Tstruct _env_md_st noattr) dvals (type_of_ctx CTX))
  POST [ tvoid ]
          PROP() LOCAL () 
          SEP(data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
              postInit nid (Int.unsigned ctxsz) (mddata_of_ctx CTX);
              data_at dsh (Tstruct _env_md_st noattr) dvals (type_of_ctx CTX)).

Inductive EVP_DigestInit_ex_case :=
  Initialized: forall (tsh:share) (vals:reptype (Tstruct _env_md_st noattr)), EVP_DigestInit_ex_case
(*Adam: InitiatlizedDigestSet case fails, if ctx->digest = type*)
| HashFinishedEQ: forall (tsh:share) (vals:reptype (Tstruct _env_md_st noattr)), EVP_DigestInit_ex_case
| HashFinishedNEQ: forall (tsh dsh:share) (vals dvals:reptype (Tstruct _env_md_st noattr)) (d:val), EVP_DigestInit_ex_case.

(*
Axiom Adam1: forall ctx t, 
  field_at Tsh (Tstruct _env_md_ctx_st noattr) [] (t, (nullval, (nullval, nullval))) ctx
  |-- data_at Tsh (Tstruct _env_md_ctx_st noattr) (nullval, (nullval, (nullval, nullval))) ctx.
*)

Definition EVP_DigestInit_ex_pre (c:EVP_DigestInit_ex_case) (t ctx:val): mpred :=
  match c with
    Initialized tsh vals =>
      EX nid:int, EX ctxsz: int, 
      !!(get_ctxsize vals = Vint ctxsz /\ get_type vals = Vint nid /\
         4 <= Int.unsigned ctxsz <= Int.max_unsigned /\ is_pointer_or_null (get_iniptr vals) )
      && EVP_MD_NNnode tsh vals t * func_ptr' ini_spec (get_iniptr vals) *
         MDCTXInitialized ctx
  | HashFinishedEQ tsh vals => EVP_MD_NNnode tsh vals t * func_ptr' ini_spec (get_iniptr vals) *
      EX nid: int, EX ctxsz: int,
         !!(get_ctxsize vals = Vint ctxsz /\ get_type vals = Vint nid /\
            4 < Int.unsigned ctxsz <= Int.max_unsigned /\ is_pointer_or_null (get_iniptr vals))
         && (MDCTXFinished nid ctxsz t ctx || EX data:_, MDCTXHashed nid ctxsz data t ctx)
  | HashFinishedNEQ tsh dsh vals dvals d => 
      EX nid:int, EX ctxsz:int,
      !!(get_ctxsize vals = Vint ctxsz /\ get_type vals = Vint nid /\
         4 <= Int.unsigned ctxsz <= Int.max_unsigned /\ is_pointer_or_null (get_iniptr vals) )
      &&
      EVP_MD_NNnode tsh vals t * func_ptr' ini_spec (get_iniptr vals) * EVP_MD_NNnode dsh dvals d *
      EX nid': int, EX ctxsz': int,
         !!(d<>t /\ get_ctxsize dvals = Vint ctxsz' /\ get_type dvals = Vint nid' /\
            0 < Int.unsigned ctxsz' <= Int.max_unsigned)
         && (MDCTXFinished nid' ctxsz' d ctx || EX data:_, MDCTXHashed nid' ctxsz' data d ctx)
end.

Definition EVP_DigestInit_ex_post (c:EVP_DigestInit_ex_case) (t ctx rv:val): mpred :=
  match c with
    Initialized tsh vals => EVP_MD_NNnode tsh vals t * func_ptr' ini_spec (get_iniptr vals) * 
          (    (!!(rv=Vzero) && MDCTXInitializedDigestSet t ctx)
            || (!!(rv=Vone) && EX nid: int, EX ctxsz: int,
                !!(get_ctxsize vals = Vint ctxsz /\ get_type vals = Vint nid) 
                && MDCTXConfigured nid ctxsz t ctx) )
  | HashFinishedEQ tsh vals => !!(rv=Vone) &&
      EX nid: int, EX ctxsz: int,
         !!(get_ctxsize vals = Vint ctxsz /\ get_type vals = Vint nid) 
         && MDCTXConfigured nid ctxsz t ctx * EVP_MD_NNnode tsh vals t * func_ptr' ini_spec (get_iniptr vals)
  | HashFinishedNEQ tsh dsh vals dvals d => 
      EVP_MD_NNnode tsh vals t * func_ptr' ini_spec (get_iniptr vals) * EVP_MD_NNnode dsh dvals d *
        (   (!!(rv=Vzero) && MDCTXInitializedDigestSet t ctx)
         || (!!(rv=Vone) && EX nid: int, EX ctxsz: int,
             !!(get_ctxsize vals = Vint ctxsz /\ get_type vals = Vint nid) && MDCTXConfigured nid ctxsz t ctx))
end.

Definition EVP_DigestInit_ex_SPEC := DECLARE _EVP_DigestInit_ex
  WITH ep: val, ctx:val, t:val, e:val, c:EVP_DigestInit_ex_case
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr),
        _engine OF tptr (Tstruct _engine_st noattr) ]
      PROP ()
      LOCAL (gvar ___stringlit_1 ep; temp _type t; temp _ctx ctx; temp _engine e)
      SEP (ERR ep; EVP_DigestInit_ex_pre c t ctx)
  POST [ tint] EX rv:_,
       PROP () LOCAL (temp ret_temp rv)
       SEP (ERR ep; EVP_DigestInit_ex_post c t ctx rv). 

Definition Gprog_DigestInit_ex : funspecs :=
  [OPENSSL_PUT_ERROR_SPEC; OPENSSL_free_SPEC; OPENSSL_malloc_SPEC].

Axiom body_DigestInit_ex: semax_body Vprog Gprog_DigestInit_ex f_EVP_DigestInit_ex EVP_DigestInit_ex_SPEC.

Definition EVP_DigestInit_SPEC := DECLARE _EVP_DigestInit
  WITH ep: val, ctx:val, t:val, tsh:share, 
       vals:reptype (Tstruct _env_md_st noattr), ctxsz:int, nid:int
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr) ]
      PROP (get_ctxsize vals = Vint ctxsz;
            4 <= Int.unsigned ctxsz <= Int.max_unsigned;
            is_pointer_or_null (get_iniptr vals); 
            get_type vals = Vint nid)
      LOCAL (gvar ___stringlit_1 ep; temp _type t; temp _ctx ctx)
      SEP (MDCTXAllocated ctx; ERR ep; EVP_MD_NNnode tsh vals t;
           func_ptr' ini_spec (get_iniptr vals))
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP ((!!(rv=Vzero) && MDCTXInitializedDigestSet t ctx)
            || (!!(rv=Vone) && MDCTXConfigured nid ctxsz t ctx);
            ERR ep; EVP_MD_NNnode tsh vals t; func_ptr' ini_spec (get_iniptr vals)).

Definition Gprog_DigestInit : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [EVP_DigestInit_ex_SPEC; EVP_MD_CTX_init_SPEC].

Axiom body_DigestInit: semax_body Vprog Gprog_DigestInit f_EVP_DigestInit EVP_DigestInit_SPEC.

Definition upd_spec:funspec :=
  WITH ctx: val, nid:int, ctxsz:int, old: list Z, d:val, 
       data: val, dsh:share, new: list Z, len:int
  PRE [ 1%positive OF (tptr (Tstruct _env_md_ctx_st noattr)), 
        2%positive OF tptr tvoid, 3%positive OF tuint]
       PROP (readable_share dsh)
       LOCAL (temp 1%positive ctx; temp 2%positive data; temp 3%positive (Vint len) )
       SEP (MDCTXHashed nid ctxsz old d ctx;
            data_at dsh (tarray tuchar (Int.unsigned len)) (map Vint (map Int.repr new)) data)
  POST [ tvoid ]
          PROP() LOCAL () 
          SEP(MDCTXHashed nid ctxsz (old++new) d ctx;
              data_at dsh (tarray tuchar (Int.unsigned len)) (map Vint (map Int.repr new)) data).

Definition EVP_DigestUpdate_SPEC := DECLARE _EVP_DigestUpdate
  WITH ctx: val, nid:int, ctxsz:int, old: list Z, d:val, 
       data: val, dsh:share, new: list Z, len:int, 
       tsh:share, vals:reptype (Tstruct _env_md_st noattr)
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), _data OF tptr tvoid,  _len OF tuint ]
      PROP (readable_share dsh; readable_share tsh)
      LOCAL (temp _ctx ctx; temp _data data; temp _len (Vint len) )
      SEP (MDCTXHashed nid ctxsz old d ctx;
            data_at dsh (tarray tuchar (Int.unsigned len)) (map Vint (map Int.repr new)) data;
            EVP_MD_NNnode tsh vals d;
            func_ptr' upd_spec (get_updptr vals))
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (MDCTXHashed nid ctxsz (old++new) d ctx;
            data_at dsh (tarray tuchar (Int.unsigned len)) (map Vint (map Int.repr new)) data;
              EVP_MD_NNnode tsh vals d;
              func_ptr' upd_spec (get_updptr vals)).

Definition Gprog_DigestUpdate : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [].

Axiom body_DigestUpdate: semax_body Vprog Gprog_DigestUpdate f_EVP_DigestUpdate EVP_DigestUpdate_SPEC.

Definition fin_spec:funspec :=
  WITH ctx: val, nid:int, ctxsz:int, content: list Z, d:val,
       out: val, osh:share, len:Z
  PRE [ 1%positive OF tptr (Tstruct _env_md_ctx_st noattr),
        2%positive OF tptr tuchar]
       PROP (writable_share osh)
       LOCAL (temp 1%positive ctx; temp 2%positive out)
       SEP (MDCTXHashed nid ctxsz content d ctx; 
            memory_block osh len out)
  POST [ tvoid ]
          PROP() LOCAL () 
          SEP(MDCTXFinished nid ctxsz d ctx;
              data_at osh (tarray tuchar len) (map Vint (map Int.repr content)) out).

Definition EVP_DigestFinal_ex_SPEC := DECLARE _EVP_DigestFinal_ex
  WITH ctx: val, nid:int, ctxsz:int, content: list Z, d:val,
       out: val, osh:share, sz:val, tsh:share,
       vals:reptype (Tstruct _env_md_st noattr), mdsize:int
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr),
        _md_out OF tptr tuchar, _size OF tptr tuint]
      PROP (writable_share osh; readable_share tsh;
            get_mdsize vals = Vint mdsize;
            get_ctxsize vals = Vint ctxsz; 0 <= Int.unsigned ctxsz <= Int.max_unsigned)
      LOCAL (temp _ctx ctx; temp _md_out out; temp _size sz)
      SEP (MDCTXHashed nid ctxsz content d ctx; 
            memory_block osh (Int.unsigned mdsize) out;
            EVP_MD_NNnode tsh vals d;
            func_ptr' fin_spec (get_finptr vals); 
            if Val.eq sz nullval then emp else data_at_ Tsh tuint sz)
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (MDCTXFinished nid ctxsz d ctx;
              data_at osh (tarray tuchar (Int.unsigned mdsize)) (map Vint (map Int.repr content)) out;
              EVP_MD_NNnode tsh vals d;
              func_ptr' fin_spec (get_finptr vals);
              if Val.eq sz nullval then emp else data_at Tsh tuint (Vint mdsize) sz).

Definition Gprog_DigestFinal_ex : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [OPENSSL_cleanse_SPEC].

Axiom body_DigestFinal_ex: semax_body Vprog Gprog_DigestFinal_ex f_EVP_DigestFinal_ex EVP_DigestFinal_ex_SPEC.

Definition EVP_DigestFinal_SPEC := DECLARE _EVP_DigestFinal
  WITH ctx: val, nid:int, ctxsz:int, content: list Z, d:val,
       out: val, osh:share, sz:val, tsh:share,
       vals:reptype (Tstruct _env_md_st noattr), mdsize:int
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr),
        _md OF tptr tuchar, _size OF tptr tuint]
      PROP (writable_share osh; readable_share tsh;
            get_mdsize vals = Vint mdsize;
            get_ctxsize vals = Vint ctxsz; 0 <= Int.unsigned ctxsz <= Int.max_unsigned;
            get_type vals = Vint nid)
      LOCAL (temp _ctx ctx; temp _md out; temp _size sz)
      SEP (MDCTXHashed nid ctxsz content d ctx; 
            memory_block osh (Int.unsigned mdsize) out;
            EVP_MD_NNnode tsh vals d;
            func_ptr' fin_spec (get_finptr vals); 
            if Val.eq sz nullval then emp else data_at_ Tsh tuint sz)
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (MDCTXInitialized ctx; EVP_MD_NNnode tsh vals d;
            data_at osh (tarray tuchar (Int.unsigned mdsize)) (map Vint (map Int.repr content)) out;
            func_ptr' fin_spec (get_finptr vals);
            if Val.eq sz nullval then emp else data_at Tsh tuint (Vint mdsize) sz).

Definition Gprog_DigestFinal : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [EVP_DigestFinal_ex_SPEC; EVP_MD_CTX_cleanup_SPEC].

Axiom body_DigestFinal: semax_body Vprog Gprog_DigestFinal f_EVP_DigestFinal EVP_DigestFinal_SPEC.


(*Adam2: State MDCTXAllocated ictx must be ruled out, ie if ictx is nonnull, 
  it must also be initialized already. Otherwise the access to 
  in -> digest in the first conditional will access a Vundef.
  (Alternative: we change the def of Allocated...)*)

Definition Gprog_copy_ex : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [EVP_MD_CTX_cleanup_SPEC; OPENSSL_PUT_ERROR_SPEC; OPENSSL_malloc_SPEC; OPENSSL_memcpy_STRONGSPEC ].
(*note use of strongspec here! Without it, we'd have to prove a lemma like the following (and maybe its inverse)
  (Of course, such a lemma may be needed to justify memcpy strongspec...
Lemma DigestRep_changeREP tp v data md
  (D: DigestRep tp v (map Int.unsigned data)):
  data_at Tsh tp v md = data_at Tsh (tarray tuchar (sizeof tp)) (map Vint data) md.
Admitted.*)

Inductive EVP_MD_CTX_copy_case :=
  CopyInitialized: EVP_MD_CTX_copy_case
| CopyHashedFinished: forall (dsh:share) (vals:reptype (Tstruct _env_md_st noattr))
                             (data: option (list int)) (d:val), EVP_MD_CTX_copy_case.

Definition EVP_MD_CTX_copy_pre (c:EVP_MD_CTX_copy_case) (octx ictx:val) : mpred :=
  match c with
   CopyInitialized => MDCTXInitialized ictx
 | CopyHashedFinished dsh vals data d => 
     EX nid:int, EX ctxsz:int, 
     !!(get_ctxsize vals = Vint ctxsz /\ 4 <= Int.unsigned ctxsz <= Int.max_unsigned)
     && match data with None => MDCTXFinished nid ctxsz d ictx
                     | Some v => MDCTXHashed nid ctxsz (map Int.unsigned v) d ictx
        end * 
        EVP_MD_NNnode dsh vals d * MDCTXInitialized octx
 end.

Definition EVP_MD_CTX_copy_post (c:EVP_MD_CTX_copy_case) (octx ictx rv:val) : mpred :=
  match c with
   CopyInitialized => !!(rv=nullval)&& MDCTXInitialized ictx
 | CopyHashedFinished dsh vals data d => 
     EX nid:int, EX ctxsz:int, 
     !!(get_ctxsize vals = Vint ctxsz /\ 4 <= Int.unsigned ctxsz <= Int.max_unsigned)
     && match data with None => MDCTXFinished nid ctxsz d ictx
                     | Some v => MDCTXHashed nid ctxsz (map Int.unsigned v) d ictx
        end * EVP_MD_NNnode dsh vals d *
        ( (!!(rv=nullval) && MDCTXInitializedDigestSet d octx)
          || (!!(rv=Vone) && match data with None => MDCTXFinished nid ctxsz d octx
                                           | Some v => MDCTXHashed nid ctxsz (map Int.unsigned v) d octx
                             end ))
 end.

Definition EVP_MD_CTX_copy_ex_SPEC := DECLARE _EVP_MD_CTX_copy_ex
  WITH ep: val, octx:val, ictx:val, c: EVP_MD_CTX_copy_case
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP ()
      LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
      SEP (ERR ep; EVP_MD_CTX_copy_pre c octx ictx)
  POST [ tint] EX rv:val,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERR ep; EVP_MD_CTX_copy_post c octx ictx rv).

Axiom body_EVP_MD_CTX_copy_ex: semax_body Vprog Gprog_copy_ex f_EVP_MD_CTX_copy_ex EVP_MD_CTX_copy_ex_SPEC.

(*Also supports Hashed octx, since Hashed octx |-- Finished octx. (BUT THAT'S NOT EXPOSED!
  Allocation is performed, and result may be Vone or Vnull*)
Definition EVP_MD_CTX_copy_ex_SPEC_Finished_NEQ := DECLARE _EVP_MD_CTX_copy_ex
  WITH ep: val, octx:val, ictx:val,
       nid:int, ctxsz:int, sh:share * share, vals:_, t:val,
       nid':int, ctxsz':int, d:val
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (get_ctxsize (snd vals) = Vint ctxsz' /\ get_type (snd vals) = Vint nid';
            get_ctxsize (fst vals) = Vint ctxsz; 4 <= Int.unsigned ctxsz <= Int.max_unsigned; d<>t)
      LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
      SEP (ERR ep; MDCTXFinished nid' ctxsz' d octx; 
           MDCTXFinished nid ctxsz t ictx;
           EVP_MD_NNnode (fst sh) (fst vals) t; EVP_MD_NNnode (snd sh) (snd vals) d)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERR ep; MDCTXFinished nid ctxsz t ictx; 
            EVP_MD_NNnode (fst sh) (fst vals) t; EVP_MD_NNnode (snd sh) (snd vals) d;
            (!!(rv=nullval) && MDCTXInitializedDigestSet t octx) 
            || (!!(rv=Vone) && MDCTXFinished nid ctxsz t octx)).

(*Also supports Hashed octx, since Hashed octx |-- Finished octx.
  No allocation is performed, and result value is always Vone*)
Definition EVP_MD_CTX_copy_ex_SPEC_Finished_EQ := DECLARE _EVP_MD_CTX_copy_ex
  WITH ep: val, octx:val, ictx:val,
       nid:int, ctxsz:int, tsh:share, vals:_, t:val
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (get_ctxsize vals = Vint ctxsz; 4 <= Int.unsigned ctxsz <= Int.max_unsigned)
      LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
      SEP (ERR ep; MDCTXFinished nid ctxsz t octx; 
           MDCTXFinished nid ctxsz t ictx;
           EVP_MD_NNnode tsh vals t)
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp Vone)
       SEP (ERR ep; MDCTXFinished nid ctxsz t ictx; EVP_MD_NNnode tsh vals t;
            MDCTXFinished nid ctxsz t octx).

Axiom body_EVP_MD_CTX_copy_ex_Finished_NEQ: semax_body Vprog Gprog_copy_ex f_EVP_MD_CTX_copy_ex EVP_MD_CTX_copy_ex_SPEC_Finished_NEQ.

Axiom body_EVP_MD_CTX_copy_ex_FinishedEQ: semax_body Vprog Gprog_copy_ex f_EVP_MD_CTX_copy_ex EVP_MD_CTX_copy_ex_SPEC_Finished_EQ.

(*Also supports Hashed octx, since Hashed octx |-- Finished octx.
  Allocation is performed, and result may be Vone or Vnull*)
Definition EVP_MD_CTX_copy_ex_SPEC_Hashed_NEQ := DECLARE _EVP_MD_CTX_copy_ex
  WITH ep: val, octx:val, ictx:val,
       nid:int, ctxsz:int , data:list int, sh:share * share, vals:_, t:val,
       nid':int, ctxsz':int, d:val
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (get_ctxsize (snd vals) = Vint ctxsz' /\ get_type (snd vals) = Vint nid';
            get_ctxsize (fst vals) = Vint ctxsz; 4 <= Int.unsigned ctxsz <= Int.max_unsigned; d<>t)
      LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
      SEP (ERR ep; MDCTXFinished nid' ctxsz' d octx; 
           MDCTXHashed nid ctxsz (map Int.unsigned data) t ictx;
           EVP_MD_NNnode (fst sh) (fst vals) t; EVP_MD_NNnode (snd sh) (snd vals) d)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERR ep; MDCTXHashed nid ctxsz (map Int.unsigned data) t ictx; 
            EVP_MD_NNnode (fst sh) (fst vals) t; EVP_MD_NNnode (snd sh) (snd vals) d;
            (!!(rv=nullval) && MDCTXInitializedDigestSet t octx) 
            || (!!(rv=Vone) && MDCTXHashed nid ctxsz (map Int.unsigned data) t octx)).

(*Also supports Hashed octx, since Hashed octx |-- Finished octx.
  No allocation is performed, and result value is always Vone*)
Definition EVP_MD_CTX_copy_ex_SPEC_Hashed_EQ := DECLARE _EVP_MD_CTX_copy_ex
  WITH ep: val, octx:val, ictx:val,
       nid:int, ctxsz:int, data:list int, tsh:share, vals:_, t:val
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (get_ctxsize vals = Vint ctxsz; 4 <= Int.unsigned ctxsz <= Int.max_unsigned)
      LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
      SEP (ERR ep; MDCTXFinished nid ctxsz t octx; 
           MDCTXHashed nid ctxsz (map Int.unsigned data) t ictx;
           EVP_MD_NNnode tsh vals t)
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp Vone)
       SEP (ERR ep; MDCTXHashed nid ctxsz (map Int.unsigned data) t ictx; EVP_MD_NNnode tsh vals t;
            MDCTXHashed nid ctxsz (map Int.unsigned data) t octx).


Axiom body_EVP_MD_CTX_copy_ex_Hashed_NEQ: semax_body Vprog Gprog_copy_ex f_EVP_MD_CTX_copy_ex EVP_MD_CTX_copy_ex_SPEC_Hashed_NEQ.

Axiom body_EVP_MD_CTX_copy_ex_HashedEQ: semax_body Vprog Gprog_copy_ex f_EVP_MD_CTX_copy_ex EVP_MD_CTX_copy_ex_SPEC_Hashed_EQ.

End EVP_MD_CTX_Protocol_TP.

Module EVP_MD_CTX_Protocol <: EVP_MD_CTX_Protocol_TP.

Definition MDCTXInitialized p : mpred := 
  data_at Tsh (Tstruct _env_md_ctx_st noattr) (nullval, (nullval, (nullval, nullval))) p.

Definition MDCTXAllocated p : mpred := 
  data_at_ Tsh (Tstruct _env_md_ctx_st noattr) p.

(*Propose to Adam that this be eliminated - it's needed in 3 places*)
Definition MDCTXInitializedDigestSet t p : mpred := 
  !!(isptr t) && data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (nullval, (nullval, nullval))) p.

Lemma MDCTXAllocated_valid_ptr p: MDCTXAllocated p |-- valid_pointer p.
Proof. unfold MDCTXAllocated. apply data_at_valid_ptr; [ intuition | simpl; omega]. Qed.

Lemma MDCTXInitialized_MDCTXAllocated p: MDCTXInitialized p|-- MDCTXAllocated p.
Proof. unfold MDCTXInitialized, MDCTXAllocated; cancel. Qed.

Lemma MDCTXInitializedDigestSet_MDCTXAllocated t p: MDCTXInitializedDigestSet t p|-- MDCTXAllocated p.
Proof. unfold MDCTXInitializedDigestSet, MDCTXAllocated. entailer!. Qed.

Lemma MDCTXInitialized_valid_ptr p: MDCTXInitialized p |-- valid_pointer p.
Proof. eapply derives_trans; [ apply MDCTXInitialized_MDCTXAllocated | apply MDCTXAllocated_valid_ptr]. Qed.

Lemma MDCTXInitializedDigestSet_valid_ptr t p: MDCTXInitializedDigestSet t p |-- valid_pointer p.
Proof. eapply derives_trans; [ apply MDCTXInitializedDigestSet_MDCTXAllocated | apply MDCTXAllocated_valid_ptr]. Qed.

Lemma MDCTXAllocated_isptr p: MDCTXAllocated p |-- !! isptr p.
Proof. unfold MDCTXAllocated; entailer!. Qed.

Lemma MDCTXInitialized_isptr p: MDCTXInitialized p |-- !! isptr p.
Proof. eapply derives_trans; [ apply MDCTXInitialized_MDCTXAllocated | apply MDCTXAllocated_isptr]. Qed.

Lemma MDCTXInitializedDigestSet_isptr t p: MDCTXInitializedDigestSet t p |-- !! isptr p.
Proof. eapply derives_trans; [ apply MDCTXInitializedDigestSet_MDCTXAllocated | apply MDCTXAllocated_isptr]. Qed.

Lemma MDCTXAllocated_isptr' p: MDCTXAllocated p = (!!isptr p) && MDCTXAllocated p.
Proof. apply pred_ext; entailer; apply MDCTXAllocated_isptr. Qed.

Lemma MDCTXInitialized_isptr' p: MDCTXInitialized p = (!! isptr p) && MDCTXInitialized p.
Proof. apply pred_ext; entailer; apply MDCTXInitialized_isptr. Qed.

Lemma MDCTXInitializedDigestSet_isptr' t p: MDCTXInitializedDigestSet t p = (!! isptr p) && MDCTXInitializedDigestSet t p.
Proof. apply pred_ext; entailer; apply MDCTXInitializedDigestSet_isptr. Qed.

Definition EVP_MD_CTX_init_SPEC := DECLARE _EVP_MD_CTX_init
   WITH ctx:val
   PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr) ]
       PROP () LOCAL (temp _ctx ctx) SEP (MDCTXAllocated ctx)
   POST [ tvoid ]
       PROP () LOCAL () SEP (MDCTXInitialized ctx).

Definition EVP_MD_CTX_create_SPEC := DECLARE _EVP_MD_CTX_create
   WITH ctx:val
   PRE [ ]
       PROP () LOCAL ( ) SEP ()
   POST [ tptr (Tstruct _env_md_ctx_st noattr) ]
     EX ctx:val,
       PROP ()
       LOCAL (temp ret_temp ctx)
       SEP ((!!(ctx=nullval) && emp) || MDCTXInitialized ctx).

Definition Gprog_EVPMDCTX_1 : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [EVP_MD_CTX_create_SPEC; EVP_MD_CTX_init_SPEC; OPENSSL_memset_SPEC; OPENSSL_malloc_SPEC].

Lemma body_EVP_MD_CTX_init: semax_body Vprog Gprog_EVPMDCTX_1 f_EVP_MD_CTX_init EVP_MD_CTX_init_SPEC.
Proof.
  start_function. unfold MDCTXAllocated. simpl in *; subst.
  rewrite data_at__memory_block; simpl; Intros.
  forward_call (ctx, 16, Int.zero, memsetNonnull Tsh). entailer!. 
  forward. unfold MDCTXInitialized. apply convert.
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
+ replace_SEP 0 (MDCTXAllocated v).
  { unfold MDCTXAllocated.
    rewrite memory_block_data_at_ by (apply malloc_compatible_field_compatible; simpl; trivial; exists 2; reflexivity).
    entailer!. }
  forward_if (PROP ( ) LOCAL (temp _ctx v)  SEP (MDCTXInitialized v)). 
  - apply denote_tc_test_eq_split; [apply MDCTXAllocated_valid_ptr |  apply valid_pointer_null].
  - forward_call (v). entailer!.
  - subst; contradiction. 
  - forward. Exists v; entailer!. apply orp_right2; trivial. 
Qed.

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

Definition Gprog_cleanup : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [OPENSSL_cleanse_SPEC; OPENSSL_free_SPEC; EVP_MD_CTX_init_SPEC].

Parameter struct_of_nid: int -> option type.
Parameter DigestRep: forall (t:type) (v:reptype t) (data:list Z), Prop. (*should generalize s256_relate*)
Parameter DigestRepNil: forall t, DigestRep t (default_val t) [].

Definition postInit (nid:int) (ctxsz:Z) (p:val):mpred :=
  EX t:type, !!(struct_of_nid nid = Some t /\ sizeof t = ctxsz)
     && data_at_ Tsh t p.
Lemma postInit_memblock nid ctxsz m:
  postInit nid (Int.unsigned ctxsz) m |-- memory_block Tsh (Int.unsigned ctxsz) m.
Proof. unfold postInit; Intros t. rewrite data_at__memory_block, H0; entailer!. Qed.

Definition MDCTXConfigured nid ctxsz (d p:val): mpred :=
  EX md:val, !!(Int.eq ctxsz Int.zero=false) && EVP_MD_CTX_NNnode Tsh (d,(md,(nullval,nullval))) p *
             postInit nid (Int.unsigned ctxsz) md.

Definition MDCTXHashed nid ctxsz (data:list Z) (d p:val): mpred :=
  EX md:val, EX t:type, EX v: reptype t,
       !!(Int.eq ctxsz Int.zero=false /\ struct_of_nid nid = Some t /\ sizeof t = Int.unsigned ctxsz /\
          DigestRep t v data)
       && EVP_MD_CTX_NNnode Tsh (d,(md,(nullval,nullval))) p *
             data_at Tsh t v md.

Definition MDCTXFinished nid ctxsz (d p:val): mpred :=
  EX md:val, EX t:type, 
       !!(Int.eq ctxsz Int.zero=false /\ struct_of_nid nid = Some t /\ sizeof t = Int.unsigned ctxsz)
       && EVP_MD_CTX_NNnode Tsh (d,(md,(nullval,nullval))) p *
             data_at_ Tsh t md.

Lemma MDCTXConfigured_valid_ptr nid ctxsz d p: MDCTXConfigured nid ctxsz d p |-- valid_pointer p.
Proof. unfold MDCTXConfigured, EVP_MD_CTX_NNnode; entailer. Qed.

Lemma MDCTXConfigured_isptr nid ctxsz d p: MDCTXConfigured ctxsz nid d p |-- !! isptr p.
Proof. unfold MDCTXConfigured. normalize. rewrite EVP_MD_CTX_NNnode_isptr'. entailer!. Qed.

Lemma MDCTXConfigured_isptr' nid ctxsz d p: MDCTXConfigured nid ctxsz d p = (!!isptr p) && MDCTXConfigured nid ctxsz d p.
Proof. apply pred_ext; entailer; apply MDCTXConfigured_isptr. Qed.

Lemma MDCTXHashed_MDCTXConfigured nid ctxsz data d p: MDCTXHashed nid ctxsz data d p |-- MDCTXConfigured nid ctxsz d p.
Proof. unfold MDCTXHashed, MDCTXConfigured. Intros md t v. Exists md; entailer!. Exists t; entailer!. Qed.

Lemma MDCTXHashed_valid_ptr nid ctxsz data d p: MDCTXHashed nid ctxsz data d p |-- valid_pointer p.
Proof. eapply derives_trans; [ apply MDCTXHashed_MDCTXConfigured | apply MDCTXConfigured_valid_ptr]. Qed.

Lemma MDCTXHashed_isptr nid ctxsz data d p: MDCTXHashed nid ctxsz data d p |-- !! isptr p.
Proof. eapply derives_trans; [ apply MDCTXHashed_MDCTXConfigured | apply MDCTXConfigured_isptr]. Qed.

Lemma MDCTXHashed_isptr' nid ctxsz data d p:
      MDCTXHashed nid ctxsz data d p = (!!isptr p) && MDCTXHashed nid ctxsz data d p.
Proof. apply pred_ext; entailer; apply MDCTXHashed_isptr. Qed.

Lemma MDCTXConfigured_MDCTXHashed nid ctxsz d p: MDCTXConfigured nid ctxsz d p |-- MDCTXHashed nid ctxsz nil d p.
Proof. unfold MDCTXHashed, MDCTXConfigured, postInit; Intros md t.
  Exists md t (default_val t); entailer!. apply DigestRepNil. 
Qed.

(*This lemma is not to be exposed!*)
Lemma MDCTXFinished_MDCTXConfigured nid ctxsz d p: MDCTXFinished nid ctxsz d p = MDCTXConfigured nid ctxsz d p.
Proof. unfold MDCTXFinished, MDCTXConfigured, postInit; apply pred_ext; Intros md t; Exists md t; entailer!. Qed.

(*This lemma is not to be exposed!*)
Lemma MDCTXHashed_MDCTXFinished nid ctxsz data d p: MDCTXHashed nid ctxsz data d p |-- MDCTXFinished nid ctxsz d p.
Proof. unfold MDCTXFinished, MDCTXHashed; Intros md t v. Exists md t; entailer!. Qed.

Lemma MDCTXFinished_valid_ptr nid ctxsz d p: MDCTXFinished nid ctxsz d p |-- valid_pointer p.
Proof. rewrite MDCTXFinished_MDCTXConfigured. apply MDCTXConfigured_valid_ptr. Qed.

Lemma MDCTXFinished_isptr nid ctxsz d p: MDCTXFinished nid ctxsz d p |-- !! isptr p.
Proof. rewrite MDCTXFinished_MDCTXConfigured. apply MDCTXConfigured_isptr. Qed.

Lemma MDCTXFinished_isptr' nid ctxsz d p:
      MDCTXFinished nid ctxsz d p = (!!isptr p) && MDCTXFinished nid ctxsz d p.
Proof. apply pred_ext; entailer; apply MDCTXFinished_isptr. Qed.

Definition MDCTXHashedOrFinished nid ctxsz d p: mpred :=
  (EX data:_, MDCTXHashed nid ctxsz (map Int.unsigned data) d p)
  || MDCTXFinished nid ctxsz d p.

Lemma MDCTXHashedOrFinished_valid_ptr nid ctxsz d p: 
      MDCTXHashedOrFinished nid ctxsz d p |-- valid_pointer p.
Proof. apply orp_left; [ Intros data; apply MDCTXHashed_valid_ptr | apply MDCTXFinished_valid_ptr ]. Qed.
 
Lemma MDCTXHashedOrFinished_isptr nid ctxsz d p: 
  MDCTXHashedOrFinished nid ctxsz d p |-- !!(isptr p).
Proof.
  apply orp_left; [ Intros data; apply MDCTXHashed_isptr | apply MDCTXFinished_isptr ]. 
Qed.
Lemma MDCTXHashedOrFinished_isptr' nid ctxsz d p: 
  MDCTXHashedOrFinished nid ctxsz d p = !!(isptr p) && MDCTXHashedOrFinished nid ctxsz d p.
Proof. apply pred_ext; entailer; apply MDCTXHashedOrFinished_isptr. Qed.

(*This lemma is not exposed*)
Lemma MDCTXHashedOrFinished_MDCTXFinished nid ctxsz d p: 
  MDCTXHashedOrFinished nid ctxsz d p = MDCTXFinished nid ctxsz d p.
Proof. apply pred_ext.
  apply orp_left; [ Intros data; apply MDCTXHashed_MDCTXFinished | trivial].
  apply orp_right2; trivial.
Qed.

Inductive EVP_MD_CTX_cleanup_case :=
  ClInitialized: EVP_MD_CTX_cleanup_case
| ClInitializedDigestSet: forall (d:val) (dsh:share) (vals:reptype (Tstruct _env_md_st noattr)), EVP_MD_CTX_cleanup_case (*Talk with Adam to allow removal of this*)
| ClConfiguredOrFinished: forall (dsh:share) (vals:reptype (Tstruct _env_md_st noattr)) (d:val), EVP_MD_CTX_cleanup_case.

Definition EVP_MD_CTX_cleanup_pre (c:EVP_MD_CTX_cleanup_case) (ctx:val) : mpred :=
  match c with
   ClInitialized => MDCTXInitialized ctx
 | ClInitializedDigestSet t tsh vals => EX ctxsz:int, 
     !!(get_ctxsize vals = Vint ctxsz /\ Int.eq ctxsz Int.zero = false)
     && MDCTXInitializedDigestSet t ctx * EVP_MD_NNnode tsh vals t
 | ClConfiguredOrFinished dsh vals d => 
     EX nid:int, EX ctxsz:int, 
     !!(get_ctxsize vals = Vint ctxsz /\ get_type vals = Vint nid)
     && (MDCTXConfigured nid ctxsz d ctx || MDCTXFinished nid ctxsz d ctx) * EVP_MD_NNnode dsh vals d
end.

Definition EVP_MD_CTX_cleanup_post (c:EVP_MD_CTX_cleanup_case) (ctx:val) : mpred :=
  match c with
   ClInitialized => MDCTXInitialized ctx
 | ClInitializedDigestSet t tsh vals => MDCTXInitialized ctx * EVP_MD_NNnode tsh vals t
 | ClConfiguredOrFinished dsh vals d => MDCTXInitialized ctx * EVP_MD_NNnode dsh vals d
end.

Definition EVP_MD_CTX_cleanup_SPEC := DECLARE _EVP_MD_CTX_cleanup
  WITH ctx:val, c:EVP_MD_CTX_cleanup_case
  PRE [ _ctx OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP () LOCAL (temp _ctx ctx)
      SEP (EVP_MD_CTX_cleanup_pre c ctx)
  POST [ tint ]
       PROP () LOCAL (temp ret_temp (Vint (Int.one)))
       SEP (EVP_MD_CTX_cleanup_post c ctx).

Lemma body_EVP_MD_CTX_cleanup: semax_body Vprog Gprog_cleanup f_EVP_MD_CTX_cleanup EVP_MD_CTX_cleanup_SPEC.
Proof. 
  start_function. destruct c; simpl.
+ (*Initialized*)
  unfold MDCTXInitialized. forward. 
  forward_if (
    PROP ( )
    LOCAL (temp _t'1 (Vint Int.zero); temp _ctx ctx)
    SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (nullval, (nullval, (nullval, nullval))) ctx));
    [ simpl in H; contradiction | clear H; forward; entailer! | ].
  forward_if (
    PROP ( )
    LOCAL (temp _t'2 (Vint Int.zero); temp _ctx ctx)
    SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (nullval, (nullval, (nullval, nullval))) ctx));
    [ elim H; trivial | clear H; forward; entailer! | ].
  forward_if (
     PROP ( )
     LOCAL (temp _ctx ctx)
     SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (nullval, (nullval, (nullval, nullval))) ctx));
    [ elim H; trivial | clear H; forward; entailer! | ].
  forward.
  forward_if (
     PROP ( )
     LOCAL (temp _ctx ctx)
     SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (nullval, (nullval, (nullval, nullval))) ctx));
    [ inv H | clear H; forward; entailer! | ].
  forward_call (ctx). { unfold MDCTXAllocated. cancel. }
  forward.
+ (*InitializedDigestSet*)
  unfold MDCTXInitializedDigestSet, EVP_MD_NNnode; Intros ctxsz.
  rename H into SZ. rename H0 into SZ1. rename H1 into DSH. forward.
  forward_if (
    PROP ( )
    LOCAL (temp _t'1 (Vint Int.one); temp _ctx ctx)
    SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, nullval))) ctx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)).
    { clear H. forward.
      destruct vals as [tp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
      forward. forward. entailer!. simpl; rewrite SZ1; trivial. }
    { subst; contradiction. }  
  forward_if (
    PROP ( )
    LOCAL (temp _t'2 Vzero; temp _ctx ctx)
    SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, nullval))) ctx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)). 
    { clear; forward. forward. entailer!. }
    { inv H. }
  forward_if (
    PROP ( )
    LOCAL (temp _ctx ctx)
    SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, nullval))) ctx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)).
    { elim H; trivial. }
    { clear H; forward; entailer!. }
  forward.
  forward_if (
    PROP ( )
    LOCAL (temp _ctx ctx)
    SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, nullval))) ctx;
         data_at dsh (Tstruct _env_md_st noattr) vals d)).
    { contradiction. }
    { clear H; forward; entailer!. }
  forward_call (ctx). { unfold MDCTXAllocated. cancel. }
  forward. unfold EVP_MD_NNnode; entailer!.
+ (*ConfiguredOrFinished*)
  Intros nid ctxsz. rename H into SZ. rename H0 into HNID.
  rewrite MDCTXFinished_MDCTXConfigured, orp_dup.
  rewrite EVP_MD_NNnode_isptr', MDCTXConfigured_isptr'; Intros.
  unfold MDCTXConfigured, EVP_MD_CTX_NNnode, EVP_MD_NNnode; Intros md.
  rename H into DSH. rename H0 into SZ2.
  unfold postInit; Intros tp. rename H into HTP. rename H0 into SZ3.
  rewrite data_at__isptr; Intros. clear PNd PNmd.
  assert (SZ4: 0 < Int.unsigned ctxsz <= Int.max_unsigned).
  { specialize (Int.unsigned_range_2 ctxsz); intros.
    destruct (zeq 0 (Int.unsigned ctxsz)); [| omega].
    apply int_eq_false_e in SZ2. elim SZ2. unfold Int.zero. 
    rewrite e, Int.repr_unsigned; trivial. } 
  forward.
  destruct vals as [tp' [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
  forward_if (
    PROP ( )
    LOCAL (temp _t'1 (Vint Int.one); temp _ctx ctx)
    SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ctx;
         memory_block Tsh (Int.unsigned ctxsz) md;
         data_at dsh (Tstruct _env_md_st noattr)
           (Vint nid, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d));
    [ clear H | subst; contradiction | ].
  { forward. forward. forward. entailer!.
    + simpl. rewrite SZ2; trivial.
    + rewrite data_at__memory_block, <- SZ3; entailer!. }
  forward_if (
    PROP ( )
    LOCAL (temp _t'2 Vone; temp _ctx ctx)
    SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ctx;
         memory_block Tsh (Int.unsigned ctxsz) md;
         data_at dsh (Tstruct _env_md_st noattr)
           (Vint nid, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d));
    [ clear H | inv H | ].
  { forward. forward. 
    { entailer!.
      apply denote_tc_test_eq_split; try apply valid_pointer_null. 
      apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
      apply memory_block_valid_ptr; [intuition | omega]. }
    entailer!. destruct md; try contradiction; trivial. }
  forward_if (
    PROP ( )
    LOCAL (temp _ctx ctx)
    SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ctx;
         data_at dsh (Tstruct _env_md_st noattr)
           (Vint nid, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d));
    [ clear H | inv H | ].
  { forward. forward. forward.
    forward_call (md, Tsh, Int.unsigned ctxsz).
    { simpl. rewrite Int.repr_unsigned. rewrite sem_cast_neutral_ptr; trivial; entailer!. }
    { intuition. }
    forward. 
    replace_SEP 0 (!! (md = nullval) && emp || memory_block Tsh (Int.unsigned ctxsz) md).
    { entailer!. apply orp_right2. eapply derives_trans; [apply data_at_memory_block | simpl].
      rewrite Z.max_r, Z.mul_1_l; [ trivial | omega]. }
    forward_call (md, Int.unsigned ctxsz).
    entailer!. }
  forward.
  forward_if (
    PROP ( )
    LOCAL (temp _ctx ctx)
    SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ctx;
         data_at dsh (Tstruct _env_md_st noattr)
           (Vint nid, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d));
    [ contradiction | forward; entailer! |].
  forward_call (ctx). { unfold MDCTXAllocated; cancel. }
  forward. unfold EVP_MD_NNnode; entailer!.
Time Qed.

Parameter preInit: Z -> val -> mpred.
Parameter memblock_preInit: forall i m, memory_block Tsh i m |-- preInit i m.

Definition ini_spec:funspec :=
  WITH ctx: val, sh:share, 
       CTX: reptype (Tstruct _env_md_ctx_st noattr),
       dsh: share, dvals: reptype (Tstruct _env_md_st noattr), ctxsz:int, nid:int
  PRE [ 1%positive OF tptr (Tstruct _env_md_ctx_st noattr)]
          PROP (writable_share sh; readable_share dsh; get_ctxsize dvals = Vint ctxsz;
                get_type dvals = Vint nid)
          LOCAL (temp 1%positive ctx)
          SEP (data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
               preInit (Int.unsigned ctxsz) (mddata_of_ctx CTX);
               data_at dsh (Tstruct _env_md_st noattr) dvals (type_of_ctx CTX))
  POST [ tvoid ]
          PROP() LOCAL () 
          SEP(data_at sh (Tstruct _env_md_ctx_st noattr) CTX ctx;
              postInit nid (Int.unsigned ctxsz) (mddata_of_ctx CTX);
              data_at dsh (Tstruct _env_md_st noattr) dvals (type_of_ctx CTX)).

Inductive EVP_DigestInit_ex_case :=
  Initialized: forall (tsh:share) (vals:reptype (Tstruct _env_md_st noattr)), EVP_DigestInit_ex_case
(*Adam: InitiatlizedDigestSet case fails!*)
| HashFinishedEQ: forall (tsh:share) (vals:reptype (Tstruct _env_md_st noattr)), EVP_DigestInit_ex_case
| HashFinishedNEQ: forall (tsh dsh:share) (vals dvals:reptype (Tstruct _env_md_st noattr)) (d:val), EVP_DigestInit_ex_case.

(*
Axiom Adam1: forall ctx t, 
  field_at Tsh (Tstruct _env_md_ctx_st noattr) [] (t, (nullval, (nullval, nullval))) ctx
  |-- data_at Tsh (Tstruct _env_md_ctx_st noattr) (nullval, (nullval, (nullval, nullval))) ctx.
*)

Definition EVP_DigestInit_ex_pre (c:EVP_DigestInit_ex_case) (t ctx:val): mpred :=
  match c with
    Initialized tsh vals =>
      EX nid:int, EX ctxsz: int, 
      !!(get_ctxsize vals = Vint ctxsz /\ get_type vals = Vint nid /\
         4 <= Int.unsigned ctxsz <= Int.max_unsigned /\ is_pointer_or_null (get_iniptr vals) )
      && EVP_MD_NNnode tsh vals t * func_ptr' ini_spec (get_iniptr vals) *
         MDCTXInitialized ctx
  | HashFinishedEQ tsh vals => EVP_MD_NNnode tsh vals t * func_ptr' ini_spec (get_iniptr vals) *
      EX nid: int, EX ctxsz: int,
         !!(get_ctxsize vals = Vint ctxsz /\ get_type vals = Vint nid /\
            4 < Int.unsigned ctxsz <= Int.max_unsigned /\ is_pointer_or_null (get_iniptr vals))
         && (MDCTXFinished nid ctxsz t ctx || EX data:_, MDCTXHashed nid ctxsz data t ctx)
  | HashFinishedNEQ tsh dsh vals dvals d => 
      EX nid:int, EX ctxsz:int,
      !!(get_ctxsize vals = Vint ctxsz /\ get_type vals = Vint nid /\
         4 <= Int.unsigned ctxsz <= Int.max_unsigned /\ is_pointer_or_null (get_iniptr vals) )
      &&
      EVP_MD_NNnode tsh vals t * func_ptr' ini_spec (get_iniptr vals) * EVP_MD_NNnode dsh dvals d *
      EX nid': int, EX ctxsz': int,
         !!(d<>t /\ get_ctxsize dvals = Vint ctxsz' /\ get_type dvals = Vint nid' /\
            0 < Int.unsigned ctxsz' <= Int.max_unsigned)
         && (MDCTXFinished nid' ctxsz' d ctx || EX data:_, MDCTXHashed nid' ctxsz' data d ctx)
end.

Definition EVP_DigestInit_ex_post (c:EVP_DigestInit_ex_case) (t ctx rv:val): mpred :=
  match c with
    Initialized tsh vals => EVP_MD_NNnode tsh vals t * func_ptr' ini_spec (get_iniptr vals) * 
          (    (!!(rv=Vzero) && MDCTXInitializedDigestSet t ctx)
            || (!!(rv=Vone) && EX nid: int, EX ctxsz: int,
                !!(get_ctxsize vals = Vint ctxsz /\ get_type vals = Vint nid) 
                && MDCTXConfigured nid ctxsz t ctx) )
  | HashFinishedEQ tsh vals => !!(rv=Vone) &&
      EX nid: int, EX ctxsz: int,
         !!(get_ctxsize vals = Vint ctxsz /\ get_type vals = Vint nid) 
         && MDCTXConfigured nid ctxsz t ctx * EVP_MD_NNnode tsh vals t * func_ptr' ini_spec (get_iniptr vals)
  | HashFinishedNEQ tsh dsh vals dvals d => 
      EVP_MD_NNnode tsh vals t * func_ptr' ini_spec (get_iniptr vals) * EVP_MD_NNnode dsh dvals d *
        (   (!!(rv=Vzero) && MDCTXInitializedDigestSet t ctx)
         || (!!(rv=Vone) && EX nid: int, EX ctxsz: int,
             !!(get_ctxsize vals = Vint ctxsz /\ get_type vals = Vint nid) && MDCTXConfigured nid ctxsz t ctx))
end.

Definition EVP_DigestInit_ex_SPEC := DECLARE _EVP_DigestInit_ex
  WITH ep: val, ctx:val, t:val, e:val, c:EVP_DigestInit_ex_case
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr),
        _engine OF tptr (Tstruct _engine_st noattr) ]
      PROP ()
      LOCAL (gvar ___stringlit_1 ep; temp _type t; temp _ctx ctx; temp _engine e)
      SEP (ERR ep; EVP_DigestInit_ex_pre c t ctx)
  POST [ tint] EX rv:_,
       PROP () LOCAL (temp ret_temp rv)
       SEP (ERR ep; EVP_DigestInit_ex_post c t ctx rv). 

Definition Gprog_DigestInit_ex : funspecs :=
  [OPENSSL_PUT_ERROR_SPEC; OPENSSL_free_SPEC; OPENSSL_malloc_SPEC].

Lemma body_DigestInit_ex: semax_body Vprog Gprog_DigestInit_ex f_EVP_DigestInit_ex EVP_DigestInit_ex_SPEC.
Proof. 
  start_function. destruct c; simpl; Intros nid ctxsz. 
+ (*Initialized*)
  destruct vals as [tp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *. subst.
  rename H1 into SZ2. rename H2 into Pini.
  assert (SZ3: Int.unsigned ctxsz > 0) by omega.
  rewrite EVP_MD_NNnode_isptr'; unfold EVP_MD_NNnode; Intros. rename H into TSH.
  rewrite MDCTXInitialized_isptr'; Intros.
  unfold MDCTXInitialized.
  forward.
  forward_if (
     PROP ( )
     LOCAL (gvar ___stringlit_1 ep;
            temp _type t; temp _ctx ctx; temp _engine e)
     SEP (ERR ep; func_ptr' ini_spec ini;
          data_at tsh (Tstruct _env_md_st noattr) (Vint nid, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t;
          EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) &&
                  data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) ctx *
                  memory_block Tsh (Int.unsigned ctxsz) m));
    [ clear H | solve [ apply ptr_comp_Cne_f in H; simpl; trivial; subst; try contradiction; destruct t; try contradiction; trivial] |]. 
  { forward.
    forward_if (PROP ( )
      LOCAL (temp _t'1 nullval; gvar ___stringlit_1 ep; temp _type t; 
             temp _ctx ctx; temp _engine e)
      SEP (ERR ep; func_ptr' ini_spec ini;
           data_at Tsh (Tstruct _env_md_ctx_st noattr) (nullval, (nullval, (nullval, nullval))) ctx;
           data_at tsh (Tstruct _env_md_st noattr) (Vint nid, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t));
     [ solve [contradiction] | solve [forward ; entailer!] | ].
    forward_if (
      PROP ( )
      LOCAL (gvar ___stringlit_1 ep;
             temp _type t; temp _ctx ctx; temp _engine e)
      SEP (ERR ep; func_ptr' ini_spec ini;
           data_at Tsh (Tstruct _env_md_ctx_st noattr) (nullval, (nullval, (nullval, nullval))) ctx;
           data_at tsh (Tstruct _env_md_st noattr) (Vint nid, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t));
     [ elim H; trivial | forward; entailer! | ].
    forward. simpl.
    rewrite eval_cast_neutral_isptr; trivial; simpl.
    (*destruct vals as [tp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *. subst.*)
    forward. 
    forward_if (
      PROP ( )
      LOCAL (gvar ___stringlit_1 ep; temp _type t; 
             temp _ctx ctx; temp _engine e)
      SEP (ERR ep; func_ptr' ini_spec ini;
           data_at tsh (Tstruct _env_md_st noattr) 
              (Vint nid, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t;
           EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) &&
                  data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) ctx *
                  memory_block Tsh (Int.unsigned ctxsz) m));
      [ clear H | solve [omega] | intros ].
    { forward.
      forward_call (Int.unsigned ctxsz). rewrite Int.repr_unsigned; entailer!. 
      Intros m. forward. forward. simpl. 
      apply semax_orp_SEPx; Intros; subst.
      + (*m==null*)
        rewrite eval_cast_neutral_is_pointer_or_null; simpl; trivial.
        forward_if (PROP (False) LOCAL () SEP ()); [ clear H | solve [inv H] | intros].
        * forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                 ep, Vint (Int.repr 177)).
          forward. Exists nullval; unfold EVP_MD_NNnode. entailer!.
          apply orp_right1. unfold MDCTXInitializedDigestSet. entailer!.
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
          SEP (memory_block Tsh (Int.unsigned ctxsz) m; 
               ERR ep; func_ptr' ini_spec ini;
               data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) ctx;
               data_at tsh (Tstruct _env_md_st noattr)
                 (Vint nid, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t));
          [ clear H | solve [subst m; contradiction] | solve [clear H; forward; entailer!] | intros ].
        * apply denote_tc_test_eq_split; [ apply sepcon_valid_pointer1 | apply valid_pointer_null].
          apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
          apply memory_block_valid_ptr; [ intuition | trivial].
        * unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
          old_go_lower. clear H. destruct ek; simpl; normalize. entailer!. 
          Exists m; entailer!. } 
    unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
    old_go_lower. clear H. destruct ek; simpl; normalize. Exists m; entailer!. }
  Intros m; rename H into M. rewrite memory_block_isptr; Intros.
(*    destruct vals as [tp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
    simpl in tp, mds, flags, ini, upd, fin, ctxsize, blsize, SZ1, SZ2, Pini, HNID; subst; simpl.*)
    forward. forward.
    replace_SEP 4 (preInit (Int.unsigned ctxsz) m). { entailer!. apply memblock_preInit. } 
    forward_call (ctx, Tsh, (t, (m, (nullval, nullval))), tsh, 
                   (Vint nid, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))), 
                   ctxsz, nid).
      { simpl. cancel. } 
    simpl; forward. Exists (Vint (Int.one)); unfold EVP_MD_NNnode; entailer!.
    apply orp_right2; Exists nid ctxsz; entailer!.
    Exists m; unfold EVP_MD_CTX_NNnode; entailer!.
    apply Int.eq_false. intros N; subst. 
    unfold Int.zero in SZ3; rewrite Int.unsigned_repr in SZ3; omega.

+ (*HashedFinishedEq*)
  destruct vals as [tpT [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
  rename H1 into SZ2. rename H2 into Pini. 
  assert (SZ3: Int.unsigned ctxsz > 0) by omega.
  rewrite EVP_MD_NNnode_isptr'; unfold EVP_MD_NNnode; Intros.
  rename H into TSH. 
  assert (PNt := isptr_is_pointer_or_null _ Pt).
  replace_SEP 3 (MDCTXFinished nid ctxsz t ctx).
  { entailer!. apply orp_left; [ trivial | Intros data; apply MDCTXHashed_MDCTXFinished ]. }
  rewrite MDCTXFinished_isptr'; Intros.
  unfold MDCTXFinished, EVP_MD_CTX_NNnode; Intros md tp.
  rename H into SZ4. rename H0 into HTP. rename H1 into SZ5.
  forward. 
  forward_if (
     PROP ( )
     LOCAL (gvar ___stringlit_1 ep; temp _type t; 
            temp _ctx ctx; temp _engine e)
     SEP (func_ptr' ini_spec ini; ERR ep; 
          data_at tsh (Tstruct _env_md_st noattr) (Vint nid, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t;
          data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ctx;
          data_at_ Tsh tp md)).
  { apply ptr_comp_Cne_t in H; trivial; congruence. }
  { clear H. forward. entailer!. } 
  forward.
(*    destruct vals as [tpT [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]].
    simpl in tpT, mds, flags, ini, upd, fin, ctxsize, blsize, SZ1, SZ2, Pini, HNID; subst; simpl.*)
    forward. 
    replace_SEP 4 (preInit (Int.unsigned ctxsz) md). { rewrite data_at__memory_block; entailer!. rewrite <- SZ5. apply memblock_preInit. }
    forward_call (ctx, Tsh, (t, (md, (nullval, nullval))), tsh, 
                   (Vint nid, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))), 
                   ctxsz, nid).
      { simpl. cancel. } 
  forward.
  Exists Vone; entailer!. Exists nid ctxsz; entailer!. 
  unfold EVP_MD_NNnode, MDCTXConfigured, EVP_MD_CTX_NNnode. Exists md; entailer!.

+ (*HashedFinishedNEQ*)
  (*destruct dvals as [tpD [mdsD [flagsD [iniD [updD [finD [blsizeD ctxsizeD]]]]]]]; simpl in *; subst.*)
  destruct vals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
  rename H1 into SZ2. rename H2 into Pini.
  assert (SZ3: Int.unsigned ctxsz > 0) by omega. unfold POSTCONDITION, abbreviate.
  Intros nid' ctxsz'.
  rename H into DT. rename H0 into SZD. rename H1 into HNID'. rename H2 into SZD1.
  assert (SZD3: Int.unsigned ctxsz' > 0) by omega.
  rewrite EVP_MD_NNnode_isptr' with (p:=t).
  rewrite EVP_MD_NNnode_isptr' with (p:=d); unfold EVP_MD_NNnode; Intros.
  rename H into TSH. rename H0 into DSH.
  assert (PNt := isptr_is_pointer_or_null _ Pt).
  replace_SEP 4 (MDCTXFinished nid' ctxsz' d ctx).
  { entailer!. apply orp_left; [ trivial | Intros data; apply MDCTXHashed_MDCTXFinished ]. }
  rewrite MDCTXFinished_isptr'; Intros.
  unfold MDCTXFinished, EVP_MD_CTX_NNnode; Intros md tp.
  rename H into CTXSZ4. rename H0 into HTP. rename H1 into TPSZ.
  freeze [1] T. forward. 
  forward_if (
     PROP ( )
     LOCAL (gvar ___stringlit_1 ep; temp _type t; 
            temp _ctx ctx; temp _engine e)
     SEP (func_ptr' ini_spec ini; ERR ep; FRZL T; 
          data_at dsh (Tstruct _env_md_st noattr) dvals d;
          EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m) &&
                  data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) ctx *
                  memory_block Tsh (Int.unsigned ctxsz) m)).
  { clear H. apply denote_tc_test_eq_split; [apply sepcon_valid_pointer1 | apply sepcon_valid_pointer1].
    + apply sepcon_valid_pointer1. apply sepcon_valid_pointer2; entailer!. 
    + apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
      thaw T. apply sepcon_valid_pointer1. apply data_at_valid_ptr; [ intuition | simpl; omega]. }
  { apply ptr_comp_Cne_t in H; trivial. rename H into DneqT. 
    destruct dvals as [tpD [mdsD [flagsD [iniD [updD [finD [blsizeD ctxsizeD]]]]]]]; simpl in *; subst.
    forward. freeze [5] MD. freeze [0;1;2;3] FR1.
    forward_if (PROP ( )
      LOCAL (temp _t'1 Vone; gvar ___stringlit_1 ep; temp _type t; 
             temp _ctx ctx; temp _engine e)
      SEP (FRZL FR1;
           data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ctx;
           data_at dsh (Tstruct _env_md_st noattr) (Vint nid', (mdsD, (flagsD, (iniD, (updD, (finD, (blsizeD, Vint ctxsz'))))))) d)).
    { clear H.  forward. forward. forward. entailer!. simpl. unfold Val.of_bool.
      remember (Int.ltu (Int.repr 0) ctxsz') as b; destruct b; simpl; trivial. 
      symmetry in Heqb; apply ltu_false_inv in Heqb. rewrite Int.unsigned_repr in Heqb; omega. }
    { subst; contradiction. }
    thaw FR1. freeze [1;2;3;5] FR2.
    forward_if (
      PROP ( ) 
      LOCAL (gvar ___stringlit_1 ep; temp _type t; temp _ctx ctx; temp _engine e)
      SEP (FRZL FR2; data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, nullval))) ctx)).
    { clear H; forward.
      replace_SEP 1 ((!! (md = nullval) && emp) || memory_block Tsh (sizeof tp) md).
      { clear POSTCONDITION FR2; thaw MD. entailer!. apply orp_right2; eapply derives_trans; [ apply data_at_memory_block | trivial]. }
      forward_call (md, sizeof tp).
      forward. entailer!. }
    { inv H. }
    forward. 
    rewrite eval_cast_neutral_isptr; trivial; simpl. thaw FR2. clear MD.
    unfold POSTCONDITION, abbreviate; clear POSTCONDITION; thaw T.
    (*destruct vals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.*)
    freeze [2;3] FR2. forward.
    forward_if (
      PROP ( )
      LOCAL (gvar ___stringlit_1 ep; temp _type t; temp _ctx ctx; temp _engine e)
      SEP (ERR ep; FRZL FR2; 
           EX m:_, !!(malloc_compatible (Int.unsigned ctxsz) m)
                   && memory_block Tsh (Int.unsigned ctxsz) m *
                   data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) ctx;
           data_at tsh (Tstruct _env_md_st noattr) (Vint nid, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t)).
    { clear H. forward.
      forward_call (Int.unsigned ctxsz). { simpl. rewrite Int.repr_unsigned. apply prop_right; trivial. }
      Intros m. forward. forward.
      apply semax_orp_SEPx.
      + Intros; subst; simpl.
        forward_if (PROP (False) LOCAL () SEP ()).
        - clear H. forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                 ep, Vint (Int.repr 177)).
          forward. Exists nullval; unfold EVP_MD_NNnode; entailer!.
          thaw FR2; cancel. apply orp_right1.
          unfold MDCTXInitializedDigestSet. entailer!.
        - inv H. 
        - intros. old_go_lower; clear H. unfold overridePost. if_tac; [ subst; simpl; normalize | trivial ].
      + rewrite memory_block_isptr; Intros. rename H into M.
        rewrite sem_cast_neutral_ptr; trivial; simpl.
        forward_if (
          PROP ( )
          LOCAL (gvar ___stringlit_1 ep; temp _type t; temp _ctx ctx; temp _engine e)
          SEP (memory_block Tsh (Int.unsigned ctxsz) m; FRZL FR2; ERR ep;
               data_at tsh (Tstruct _env_md_st noattr) (Vint nid, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t;
               data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) ctx)).
        - clear H. apply denote_tc_test_eq_split; [ apply sepcon_valid_pointer1 | apply valid_pointer_null].
          apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
          apply memory_block_valid_ptr; [ intuition | omega]. 
        - subst; contradiction.
        - forward. entailer!.
        - intros. unfold POSTCONDITION, abbreviate, overridePost.
          old_go_lower. 
          clear H; if_tac; simpl; trivial; subst.
          Exists m. normalize. entailer!. }
     { omega. }
     intros. unfold POSTCONDITION, abbreviate, overridePost.
     old_go_lower. clear H. if_tac; simpl; trivial; subst.
     normalize. Exists m. entailer!. thaw FR2. cancel. }
  { apply ptr_comp_Cne_f in H; trivial; contradiction. }
  Intros m; rename H into M. rewrite memory_block_isptr; Intros. forward.
  thaw T.
    (*destruct vals as [tpT [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
    simpl in tpT, mds, flags, ini, upd, fin, ctxsize, blsize, SZ1, SZ2, Pini, HNID; subst; simpl.*)
    freeze [1;3] Dep. forward. 
    replace_SEP 4 (preInit (Int.unsigned ctxsz) m). { entailer!. apply memblock_preInit. } 
    forward_call (ctx, Tsh, (t, (m, (nullval, nullval))), tsh, 
                   (Vint nid, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))), 
                   ctxsz, nid).
      { simpl. cancel. } 
    simpl; forward. Exists (Vint (Int.one)); unfold EVP_MD_NNnode; entailer!.
    thaw Dep. cancel. apply orp_right2. Exists nid ctxsz. entailer!.
    unfold MDCTXConfigured, EVP_MD_CTX_NNnode. Exists m; entailer!.
    apply Int.eq_false. intros N; subst.
    unfold Int.zero in SZ3; rewrite Int.unsigned_repr in SZ3; omega.
Time Qed.

(*Here's a failed proof attempt for Init_ex in state MDCTXInitializedDigestSet t, 
  where t is equal to the type we want to initialize ctx to*)
Definition EVP_DigestInit_ex_SPEC_MDCTXInitializedDigestSet := DECLARE _EVP_DigestInit_ex
  WITH ep: val, ctx:val, t:val, e:val, vals:_, nid:int, ctxsz:int, tsh:share
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr),
        _engine OF tptr (Tstruct _engine_st noattr) ]
      PROP (get_ctxsize vals = Vint ctxsz; get_type vals = Vint nid;
            4 <= Int.unsigned ctxsz <= Int.max_unsigned; is_pointer_or_null (get_iniptr vals))
      LOCAL (gvar ___stringlit_1 ep; temp _type t; temp _ctx ctx; temp _engine e)
      SEP (ERR ep; EVP_MD_NNnode tsh vals t; func_ptr' ini_spec (get_iniptr vals);
           MDCTXInitializedDigestSet t ctx)
  POST [ tint] 
       PROP () LOCAL ()
       SEP (). 

Goal semax_body Vprog Gprog_DigestInit_ex f_EVP_DigestInit_ex EVP_DigestInit_ex_SPEC_MDCTXInitializedDigestSet.
Proof. 
  start_function. 
  destruct vals as [tp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *. subst.
  rename H1 into SZ2. rename H2 into Pini.
  assert (SZ3: Int.unsigned ctxsz > 0) by omega.
  rewrite EVP_MD_NNnode_isptr'; unfold EVP_MD_NNnode; Intros. rename H into TSH.
(*  rewrite MDCTXInitializedDigestSet_isptr'; Intros. *)
  unfold MDCTXInitializedDigestSet; Intros.
  forward.
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _type t; temp _ctx ctx; temp _engine e)
    SEP (ERR ep; data_at tsh (Tstruct _env_md_st noattr)
                  (Vint nid, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t;
         func_ptr' ini_spec ini;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (nullval, (nullval, nullval))) ctx)).
  { apply ptr_comp_Cne_t in H; try congruence; destruct t; try contradiction; trivial. }
  { clear H. forward; entailer!. } 
  forward. forward.
(*    replace_SEP 4 (preInit (Int.unsigned ctxsz) m). { entailer!. apply memblock_preInit. } *)
  forward_call (ctx, Tsh, (t, (nullval, (nullval, nullval))), tsh, 
                   (Vint nid, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))), 
                   ctxsz, nid).
      { simpl. admit. }
Admitted.

Definition EVP_DigestInit_SPEC := DECLARE _EVP_DigestInit
  WITH ep: val, ctx:val, t:val, tsh:share, 
       vals:reptype (Tstruct _env_md_st noattr), ctxsz:int, nid:int
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), 
        _type OF tptr (Tstruct _env_md_st noattr) ]
      PROP (get_ctxsize vals = Vint ctxsz;
            4 <= Int.unsigned ctxsz <= Int.max_unsigned;
            is_pointer_or_null (get_iniptr vals); 
            get_type vals = Vint nid)
      LOCAL (gvar ___stringlit_1 ep; temp _type t; temp _ctx ctx)
      SEP (MDCTXAllocated ctx; ERR ep; EVP_MD_NNnode tsh vals t;
           func_ptr' ini_spec (get_iniptr vals))
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP ((!!(rv=Vzero) && MDCTXInitializedDigestSet t ctx)
            || (!!(rv=Vone) && MDCTXConfigured nid ctxsz t ctx);
            ERR ep; EVP_MD_NNnode tsh vals t; func_ptr' ini_spec (get_iniptr vals)).

Definition Gprog_DigestInit : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [EVP_DigestInit_ex_SPEC; EVP_MD_CTX_init_SPEC].

Lemma body_DigestInit: semax_body Vprog Gprog_DigestInit f_EVP_DigestInit EVP_DigestInit_SPEC.
Proof. 
  start_function.
  forward_call (ctx).
  forward_call (ep, ctx, t, nullval, Initialized tsh vals).
  { simpl. Exists nid ctxsz. entailer!. }
  Intros rv; forward. Exists (Vint rv); entailer!.
  apply orp_left; normalize.
  + apply orp_right1; trivial.
  + apply orp_right2. rewrite H2 in H6; inv H6. rewrite H in H5; inv H5. entailer!.
Qed.

Definition upd_spec:funspec :=
  WITH ctx: val, nid:int, ctxsz:int, old: list Z, d:val, 
       data: val, dsh:share, new: list Z, len:int
  PRE [ 1%positive OF (tptr (Tstruct _env_md_ctx_st noattr)), 
        2%positive OF tptr tvoid, 3%positive OF tuint]
       PROP (readable_share dsh)
       LOCAL (temp 1%positive ctx; temp 2%positive data; temp 3%positive (Vint len) )
       SEP (MDCTXHashed nid ctxsz old d ctx;
            data_at dsh (tarray tuchar (Int.unsigned len)) (map Vint (map Int.repr new)) data)
  POST [ tvoid ]
          PROP() LOCAL () 
          SEP(MDCTXHashed nid ctxsz (old++new) d ctx;
              data_at dsh (tarray tuchar (Int.unsigned len)) (map Vint (map Int.repr new)) data).

Definition EVP_DigestUpdate_SPEC := DECLARE _EVP_DigestUpdate
  WITH ctx: val, nid:int, ctxsz:int, old: list Z, d:val, 
       data: val, dsh:share, new: list Z, len:int, 
       tsh:share, vals:reptype (Tstruct _env_md_st noattr)
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr), _data OF tptr tvoid,  _len OF tuint ]
      PROP (readable_share dsh; readable_share tsh)
      LOCAL (temp _ctx ctx; temp _data data; temp _len (Vint len) )
      SEP (MDCTXHashed nid ctxsz old d ctx;
            data_at dsh (tarray tuchar (Int.unsigned len)) (map Vint (map Int.repr new)) data;
            EVP_MD_NNnode tsh vals d;
            func_ptr' upd_spec (get_updptr vals))
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (MDCTXHashed nid ctxsz (old++new) d ctx;
            data_at dsh (tarray tuchar (Int.unsigned len)) (map Vint (map Int.repr new)) data;
              EVP_MD_NNnode tsh vals d;
              func_ptr' upd_spec (get_updptr vals)).

Definition Gprog_DigestUpdate : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [].

Lemma body_DigestUpdate: semax_body Vprog Gprog_DigestUpdate f_EVP_DigestUpdate EVP_DigestUpdate_SPEC.
Proof. 
  start_function. unfold EVP_MD_NNnode; Intros.
  destruct vals as [tp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]. 
  simpl in *. unfold MDCTXHashed. Intros md t v.
  rename H into CTXSZ1. rename H0 into HNID. rename H1 into CTXSZ3. rename H2 into OLD.
  unfold EVP_MD_CTX_NNnode; Intros. forward. forward. 
  forward_call (ctx, nid, ctxsz, old, d, data, dsh, new, len). 
  { unfold MDCTXHashed. Exists md t v; unfold EVP_MD_CTX_NNnode; entailer!. }
  forward. cancel. unfold EVP_MD_NNnode; entailer!.
Qed.

Definition fin_spec:funspec :=
  WITH ctx: val, nid:int, ctxsz:int, content: list Z, d:val,
       out: val, osh:share, len:Z
  PRE [ 1%positive OF tptr (Tstruct _env_md_ctx_st noattr),
        2%positive OF tptr tuchar]
       PROP (writable_share osh)
       LOCAL (temp 1%positive ctx; temp 2%positive out)
       SEP (MDCTXHashed nid ctxsz content d ctx; 
            memory_block osh len out)
  POST [ tvoid ]
          PROP() LOCAL () 
          SEP(MDCTXFinished nid ctxsz d ctx;
              data_at osh (tarray tuchar len) (map Vint (map Int.repr content)) out).

Definition EVP_DigestFinal_ex_SPEC := DECLARE _EVP_DigestFinal_ex
  WITH ctx: val, nid:int, ctxsz:int, content: list Z, d:val,
       out: val, osh:share, sz:val, tsh:share,
       vals:reptype (Tstruct _env_md_st noattr), mdsize:int
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr),
        _md_out OF tptr tuchar, _size OF tptr tuint]
      PROP (writable_share osh; readable_share tsh;
            get_mdsize vals = Vint mdsize;
            get_ctxsize vals = Vint ctxsz; 0 <= Int.unsigned ctxsz <= Int.max_unsigned)
      LOCAL (temp _ctx ctx; temp _md_out out; temp _size sz)
      SEP (MDCTXHashed nid ctxsz content d ctx; 
            memory_block osh (Int.unsigned mdsize) out;
            EVP_MD_NNnode tsh vals d;
            func_ptr' fin_spec (get_finptr vals); 
            if Val.eq sz nullval then emp else data_at_ Tsh tuint sz)
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (MDCTXFinished nid ctxsz d ctx;
              data_at osh (tarray tuchar (Int.unsigned mdsize)) (map Vint (map Int.repr content)) out;
              EVP_MD_NNnode tsh vals d;
              func_ptr' fin_spec (get_finptr vals);
              if Val.eq sz nullval then emp else data_at Tsh tuint (Vint mdsize) sz).

Definition Gprog_DigestFinal_ex : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [OPENSSL_cleanse_SPEC].

Lemma body_DigestFinal_ex: semax_body Vprog Gprog_DigestFinal_ex f_EVP_DigestFinal_ex EVP_DigestFinal_ex_SPEC.
Proof. 
  start_function. rename H into MDSIZE. rename H0 into CTXSZ. rename H1 into CTXSZ2.
  unfold EVP_MD_NNnode; Intros. unfold MDCTXHashed. Intros md t v.
  rename H into CTXSZ1. rename H0 into HNID. rename H1 into CTXSZ3. rename H2 into DREP.
  unfold EVP_MD_CTX_NNnode; Intros. 
  destruct vals as [tp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
  forward. forward. 
  forward_call (ctx, nid, ctxsz, content, d, out, osh, Int.unsigned mdsize).
  { unfold MDCTXHashed, EVP_MD_CTX_NNnode. Exists md t v; entailer!. }
  unfold MDCTXFinished, EVP_MD_CTX_NNnode. Intros md' t'.
  rewrite HNID in H; symmetry in H; inv H; clear H0.
  unfold EVP_MD_CTX_NNnode; Intros.
  forward_if (
   PROP ( )
   LOCAL (temp _t'7 fin; temp _t'6 d; temp _ctx ctx;
   temp _md_out out; temp _size sz)
   SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr)
          (d, (md', (nullval, nullval))) ctx;
        data_at_ Tsh t md';
        data_at osh (tarray tuchar (Int.unsigned mdsize)) (map Vint (map Int.repr content)) out;
        data_at tsh (Tstruct _env_md_st noattr)
          (tp, (Vint mdsize, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d;
       func_ptr' fin_spec fin;
       if Val.eq sz nullval then emp else data_at Tsh tuint (Vint mdsize) sz)).
  { clear H.
     apply denote_tc_test_eq_split; [ apply sepcon_valid_pointer2 | apply valid_pointer_null].
     destruct (Val.eq sz nullval); [subst; apply valid_pointer_null | apply data_at__valid_pointer; intuition ]. }
  { forward. forward. rewrite if_false; trivial.
    forward. rewrite if_false; trivial. entailer!. }
  { subst. forward. entailer!. }
  forward. forward. forward.
  assert_PROP (field_compatible t [] md') as FC by entailer!.
  replace_SEP 1 (memory_block Tsh (Int.unsigned ctxsz) md').
  { entailer!. rewrite data_at__memory_block. rewrite <- CTXSZ3. entailer!. } 
  forward_call (md', Tsh, Int.unsigned ctxsz).
  { simpl. rewrite Int.repr_unsigned.
    rewrite eval_cast_neutral_is_pointer_or_null; trivial; simpl. entailer!. }
  forward. cancel. unfold MDCTXFinished, EVP_MD_NNnode, EVP_MD_CTX_NNnode.
  Exists md' t; entailer!. rewrite data_at__memory_block. entailer!.
  eapply derives_trans; [ apply data_at_memory_block | simpl].
  rewrite Z.mul_1_l, Z.max_r, CTXSZ3; trivial. omega.
Qed.

Definition EVP_DigestFinal_SPEC := DECLARE _EVP_DigestFinal
  WITH ctx: val, nid:int, ctxsz:int, content: list Z, d:val,
       out: val, osh:share, sz:val, tsh:share,
       vals:reptype (Tstruct _env_md_st noattr), mdsize:int
  PRE [ _ctx OF tptr (Tstruct _env_md_ctx_st noattr),
        _md OF tptr tuchar, _size OF tptr tuint]
      PROP (writable_share osh; readable_share tsh;
            get_mdsize vals = Vint mdsize;
            get_ctxsize vals = Vint ctxsz; 0 <= Int.unsigned ctxsz <= Int.max_unsigned;
            get_type vals = Vint nid)
      LOCAL (temp _ctx ctx; temp _md out; temp _size sz)
      SEP (MDCTXHashed nid ctxsz content d ctx; 
            memory_block osh (Int.unsigned mdsize) out;
            EVP_MD_NNnode tsh vals d;
            func_ptr' fin_spec (get_finptr vals); 
            if Val.eq sz nullval then emp else data_at_ Tsh tuint sz)
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp (Vint Int.one))
       SEP (MDCTXInitialized ctx; EVP_MD_NNnode tsh vals d;
            data_at osh (tarray tuchar (Int.unsigned mdsize)) (map Vint (map Int.repr content)) out;
            func_ptr' fin_spec (get_finptr vals);
            if Val.eq sz nullval then emp else data_at Tsh tuint (Vint mdsize) sz).

Definition Gprog_DigestFinal : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [EVP_DigestFinal_ex_SPEC; EVP_MD_CTX_cleanup_SPEC].

Lemma body_DigestFinal: semax_body Vprog Gprog_DigestFinal f_EVP_DigestFinal EVP_DigestFinal_SPEC.
Proof. 
  start_function.
  forward_call (ctx, nid, ctxsz, content, d, out, osh, sz, tsh, vals, mdsize).
  forward_call (ctx, ClConfiguredOrFinished tsh vals d).
  { simpl. Exists nid ctxsz; entailer!. rewrite MDCTXFinished_MDCTXConfigured, orp_dup. cancel. }
  forward. cancel.
Qed.

(*Adam2: State MDCTXAllocated ictx must be ruled out, ie if ictx is nonnull, 
  it must also be initialized already. Otherwise the access to 
  in -> digest in the first conditional will access a Vundef.
  (Alternative: we change the def of Allocated...)
Definition EVP_MD_CTX_copy_ex_SPEC_Allocated := DECLARE _EVP_MD_CTX_copy_ex
  WITH ep: val, octx:val, ictx:val (*, case:copyEx_cases*)
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP ()
      LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
      SEP (ERR ep;MDCTXAllocated ictx)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (!!(rv=nullval)&&ERR ep(*; copyExPost case ictx octx rv*)).

Definition Gprog_copy : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [EVP_MD_CTX_init_SPEC; (*EVP_MD_CTX_copy_SPEC; *)EVP_MD_CTX_copy_ex_SPEC_Allocated].

Lemma body_EVP_MD_CTX_copy_ex: semax_body Vprog Gprog_copy f_EVP_MD_CTX_copy_ex EVP_MD_CTX_copy_ex_SPEC_Allocated.
Proof. 
  start_function. forward.
  rewrite MDCTXAllocated_isptr'; Intros.
  unfold MDCTXAllocated. 
  forward_if (
    PROP ( )
     LOCAL (temp _t'1 Vone; temp _tmp_buf (Vint (Int.repr 0));
            gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
     SEP (ERR ep; data_at_ Tsh (Tstruct _env_md_ctx_st noattr) ictx)).
  { clear H; 
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer2. apply data_at__valid_pointer; [ intuition | simpl; omega]. }
  { subst; contradiction. } 
  { forward. entailer!. *)

Definition Gprog_copy_ex : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [EVP_MD_CTX_cleanup_SPEC; OPENSSL_PUT_ERROR_SPEC; OPENSSL_malloc_SPEC; OPENSSL_memcpy_STRONGSPEC ].
(*note use of strongspec here! Without it, we'd have to prove a lemma like the following (and maybe its inverse)
  (Of course, such a lemma may be needed to justify memcpy strongspec...
Lemma DigestRep_changeREP tp v data md
  (D: DigestRep tp v (map Int.unsigned data)):
  data_at Tsh tp v md = data_at Tsh (tarray tuchar (sizeof tp)) (map Vint data) md.
Admitted.*)

Inductive EVP_MD_CTX_copy_case :=
  CopyInitialized: EVP_MD_CTX_copy_case
| CopyHashedFinished: forall (dsh:share) (vals:reptype (Tstruct _env_md_st noattr))
                             (data: option (list int)) (d:val), EVP_MD_CTX_copy_case.

Definition EVP_MD_CTX_copy_pre (c:EVP_MD_CTX_copy_case) (octx ictx:val) : mpred :=
  match c with
   CopyInitialized => MDCTXInitialized ictx
 | CopyHashedFinished dsh vals data d => 
     EX nid:int, EX ctxsz:int, 
     !!(get_ctxsize vals = Vint ctxsz /\ 4 <= Int.unsigned ctxsz <= Int.max_unsigned)
     && match data with None => MDCTXFinished nid ctxsz d ictx
                     | Some v => MDCTXHashed nid ctxsz (map Int.unsigned v) d ictx
        end * 
        EVP_MD_NNnode dsh vals d * MDCTXInitialized octx
 end.

Definition EVP_MD_CTX_copy_post (c:EVP_MD_CTX_copy_case) (octx ictx rv:val) : mpred :=
  match c with
   CopyInitialized => !!(rv=nullval)&& MDCTXInitialized ictx
 | CopyHashedFinished dsh vals data d => 
     EX nid:int, EX ctxsz:int, 
     !!(get_ctxsize vals = Vint ctxsz /\ 4 <= Int.unsigned ctxsz <= Int.max_unsigned)
     && match data with None => MDCTXFinished nid ctxsz d ictx
                     | Some v => MDCTXHashed nid ctxsz (map Int.unsigned v) d ictx
        end * EVP_MD_NNnode dsh vals d *
        ( (!!(rv=nullval) && MDCTXInitializedDigestSet d octx)
          || (!!(rv=Vone) && match data with None => MDCTXFinished nid ctxsz d octx
                                           | Some v => MDCTXHashed nid ctxsz (map Int.unsigned v) d octx
                             end ))
 end.

Definition EVP_MD_CTX_copy_ex_SPEC := DECLARE _EVP_MD_CTX_copy_ex
  WITH ep: val, octx:val, ictx:val, c: EVP_MD_CTX_copy_case
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP ()
      LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
      SEP (ERR ep; EVP_MD_CTX_copy_pre c octx ictx)
  POST [ tint] EX rv:val,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERR ep; EVP_MD_CTX_copy_post c octx ictx rv).

Lemma body_EVP_MD_CTX_copy_ex: semax_body Vprog Gprog_copy_ex f_EVP_MD_CTX_copy_ex EVP_MD_CTX_copy_ex_SPEC.
Proof. 
  start_function. forward. destruct c; simpl.
+ (*Initialized*)
  rewrite MDCTXInitialized_isptr' with (p:=ictx); Intros.
  (*  rewrite MDCTXInitialized_isptr' with (p:=octx); Intros.*)
  forward_if (
    PROP ( )
     LOCAL (temp _t'1 Vone; temp _tmp_buf (Vint (Int.repr 0));
            gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
     SEP (ERR ep; (*MDCTXInitialized octx;*) MDCTXInitialized ictx)).
  { clear H; 
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer2. apply MDCTXInitialized_valid_ptr. }
  { subst; contradiction. } 
  { unfold MDCTXInitialized. forward. forward. entailer!. }
  forward_if (PROP (False) LOCAL () SEP ()).
  { forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.repr 100),
                 ep, Vint (Int.repr 121)).
    forward. Exists nullval; entailer!. }
  { inv H. }
  normalize.
+ (*HashedFinished*)
  Intros nid ctxsz. rename H into SZ. rename H0 into SZ1.
  rewrite MDCTXInitialized_isptr'; Intros.
  assert_PROP (isptr ictx) as Pictx by
    ( destruct data; [ rewrite MDCTXHashed_isptr'; entailer! | rewrite MDCTXFinished_isptr'; entailer! ] ).
  rewrite EVP_MD_NNnode_isptr'; Intros.
  forward_if (
    PROP ( )
     LOCAL (temp _t'1 Vzero; temp _tmp_buf (Vint (Int.repr 0));
            gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
     SEP (ERR ep; MDCTXInitialized octx; 
          match data with
   | Some v => MDCTXHashed nid ctxsz (map Int.unsigned v) d ictx
   | None => MDCTXFinished nid ctxsz d ictx
   end (*MDCTXHashed nid ctxsz (map Int.unsigned data) d ictx*); EVP_MD_NNnode dsh vals d)).
  { clear H; 
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. 
    apply sepcon_valid_pointer2.
    destruct data; [ apply MDCTXHashed_valid_ptr | apply MDCTXFinished_valid_ptr ]. }
  { subst; contradiction. } 
  { clear H. unfold EVP_MD_NNnode; Intros. rename H into DSH. 
    destruct data. 
    + unfold MDCTXHashed, EVP_MD_CTX_NNnode. Intros md tp v.
      forward. forward. entailer!.
      - simpl. destruct d; try contradiction; simpl; trivial.
      - unfold MDCTXHashed, EVP_MD_NNnode, EVP_MD_CTX_NNnode. Exists md tp v; entailer!.
    + unfold MDCTXFinished, EVP_MD_CTX_NNnode. Intros md tp.
      forward. forward. entailer!.
      - simpl. destruct d; try contradiction; simpl; trivial.
      - unfold MDCTXFinished, EVP_MD_NNnode, EVP_MD_CTX_NNnode. Exists md tp; entailer!.
  }
  forward_if (
    PROP ( )
    LOCAL (temp _tmp_buf (Vint (Int.repr 0));
           gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; MDCTXInitialized octx; 
         match data with
         | Some v => MDCTXHashed nid ctxsz (map Int.unsigned v) d ictx
         | None => MDCTXFinished nid ctxsz d ictx
         end;
         EVP_MD_NNnode dsh vals d)).
  { elim H; trivial. }
  { clear H; forward; entailer!. }
  unfold MDCTXInitialized. forward.
  destruct data.
  - (*Hashed*)
    unfold MDCTXHashed; unfold EVP_MD_CTX_NNnode. Intros md tp v.
    rename H into SZ2. rename H0 into HTP. rename H1 into SZ3. rename H2 into V.
  rewrite data_at_isptr with (p:=md); Intros.
  forward.
  forward_if (
    PROP ( )
    LOCAL (temp _tmp_buf (Vint (Int.repr 0)); gvar ___stringlit_1 ep;
           temp _out octx; temp _in ictx)
    SEP (ERR ep; EVP_MD_NNnode dsh vals d;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (nullval, (nullval, (nullval, nullval))) octx;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ictx;
         data_at Tsh tp v md)).
  { clear H.
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer2. apply EVP_MD_NNnode_validptr. }
  { apply ptr_comp_Ceq_t in H; simpl; trivial; subst; contradiction. }
  { clear H. forward; entailer!. }
  forward_call (octx, ClInitialized).
  { simpl; unfold MDCTXInitialized; entailer!. }
  forward. simpl; unfold MDCTXInitialized. forward.
  simpl. rewrite sem_cast_neutral_ptr; simpl; trivial.
  forward.
  forward_if (
    PROP ( )
    LOCAL (temp _t'3 Vone; temp _tmp_buf (Vint (Int.repr 0));
           gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, nullval))) octx; 
         ERR ep; data_at Tsh tp v md; EVP_MD_NNnode dsh vals d;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ictx)).
  { clear H. 
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer2. apply data_at_valid_ptr; [intuition | omega ]. }
  { clear H. forward. 
    unfold EVP_MD_NNnode; Intros. rename H into TSH.
    destruct vals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
    forward. forward. entailer!. simpl. rewrite SZ2; trivial. 
    unfold EVP_MD_NNnode; entailer!. }
  { subst md; contradiction. }
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at Tsh tp v md; EVP_MD_NNnode dsh vals d;
         EX m :_, (!!(malloc_compatible (Int.unsigned ctxsz) m) 
             && data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (m, (nullval, nullval))) octx * 
                data_at Tsh tp v m);
         data_at Tsh (Tstruct _env_md_ctx_st noattr)
            (d, (md, (nullval, nullval))) ictx));
  [ clear H | inv H | ].
  { forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at Tsh tp v md; EVP_MD_NNnode dsh vals d;
         EX m :_, (!!(malloc_compatible (Int.unsigned ctxsz) m) 
             && data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (m, (nullval, nullval))) octx * 
                memory_block Tsh (Int.unsigned ctxsz) m);
         data_at Tsh (Tstruct _env_md_ctx_st noattr)
            (d, (md, (nullval, nullval))) ictx));
    [ contradiction | clear H |].
    { forward. unfold EVP_MD_NNnode; Intros. rename H into TSH.
      destruct vals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
      forward.
      forward_call (Int.unsigned ctxsz). simpl; rewrite Int.repr_unsigned; apply prop_right; trivial.
      Intros m. forward. forward.
      apply semax_orp_SEPx; Intros.
      + (*m=Null*)
        subst; simpl.
        forward_if ( PROP (False) LOCAL () SEP ()).
        - clear H.
          forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                 ep, Vint (Int.repr 142)).
          forward. Exists nullval. entailer!. unfold MDCTXHashed, EVP_MD_NNnode.
          Exists nid ctxsz md tp v; unfold EVP_MD_CTX_NNnode; entailer!.
          apply orp_right1. unfold MDCTXInitializedDigestSet. entailer!.
        - inv H.
        - intros. unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
          old_go_lower. clear H. destruct ek; simpl; normalize. 
      + (*m<>null*)
        rename H into M. 
        rewrite memory_block_isptr; Intros.
        rewrite eval_cast_neutral_isptr; simpl; trivial.
        forward_if (
          PROP ( )
          LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
          SEP (memory_block Tsh (Int.unsigned ctxsz) m;
               data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (m, (nullval, nullval))) octx; 
               ERR ep; data_at Tsh tp v md;
               data_at dsh (Tstruct _env_md_st noattr) (tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d;
               data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ictx)).
        - clear H.
          apply denote_tc_test_eq_split; [ apply sepcon_valid_pointer1 | apply valid_pointer_null].
          apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
          apply sepcon_valid_pointer1. apply memory_block_valid_ptr. intuition. omega.
        - destruct m; try contradiction. simpl in H. inv H.
        - clear H. forward. entailer!.
        - intros. unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
          old_go_lower. clear H. destruct ek; simpl; normalize. entailer!. 
          Exists m; unfold EVP_MD_NNnode; entailer!. }
    Intros m. rename H into M. forward. forward. forward.
    unfold EVP_MD_NNnode; Intros. rename H into TSH. 
    destruct vals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
    forward. (*
    rewrite (DigestRep_changeREP tp v data); trivial.
    replace_SEP  1 (data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint data) md).
    { entailer!. rewrite <- SZ3; trivial. } 
    forward_call ((Tsh,Tsh),m, md,Int.unsigned ctxsz, data).
         { rewrite Int.repr_unsigned; entailer!. }
         { simpl. cancel. }
         { simpl; split; trivial. intuition. split; trivial. apply Int.unsigned_range_2. }
    entailer!. Exists m; unfold EVP_MD_NNnode.
    rewrite ! (DigestRep_changeREP tp v data); trivial.
    entailer!. rewrite <- ! SZ3. cancel. }*)

    forward_call ((Tsh,Tsh),m, md,Int.unsigned ctxsz, Build_REPTYPE tp v). 
         { rewrite Int.repr_unsigned; entailer!. }
         { simpl. cancel. }
         { simpl; split; trivial. intuition. split; trivial. 
           split. apply Int.unsigned_range_2. rewrite SZ3; trivial. }
    entailer!. Exists m; unfold EVP_MD_NNnode; entailer!. }

  Intros m. rename H into M. forward. forward. forward. 
  forward_if (
    PROP ( )
    LOCAL (temp _t'5 (Vint (Int.repr 0)); gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at Tsh tp v md; EVP_MD_NNnode dsh vals d;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (m, (nullval, Vint Int.zero))) octx;
         data_at Tsh tp v m;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ictx)).
  { contradiction. }
  { clear H. forward. entailer!. }
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at Tsh tp v md; EVP_MD_NNnode dsh vals d;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (m, (nullval, Vint Int.zero))) octx;
         data_at Tsh tp v m;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ictx)).
  { contradiction. }
  { clear H. forward. entailer!. }
  forward. Exists Vone; unfold MDCTXHashed; entailer!.
  Exists nid ctxsz md tp v. unfold EVP_MD_CTX_NNnode; entailer!.
  apply orp_right2. Exists m tp v; entailer!.

  - (*Finished*)
  unfold MDCTXFinished, EVP_MD_CTX_NNnode; Intros md tp.
  rename H into SZ2. rename H0 into HTP. rename H1 into SZ3.
  rewrite data_at__isptr with (p:=md); Intros.
  forward.
  forward_if (
    PROP ( )
    LOCAL (temp _tmp_buf (Vint (Int.repr 0)); gvar ___stringlit_1 ep;
           temp _out octx; temp _in ictx)
    SEP (ERR ep; EVP_MD_NNnode dsh vals d;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (nullval, (nullval, (nullval, nullval))) octx;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ictx;
         data_at_ Tsh tp md)).
  { clear H.
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer2. apply EVP_MD_NNnode_validptr. }
  { apply ptr_comp_Ceq_t in H; simpl; trivial; subst; contradiction. }
  { clear H. forward; entailer!. }
  forward_call (octx, ClInitialized).
  { simpl; unfold MDCTXInitialized; entailer!. }
  forward. simpl; unfold MDCTXInitialized. forward.
  simpl. rewrite sem_cast_neutral_ptr; simpl; trivial.
  forward.
  forward_if (
    PROP ( )
    LOCAL (temp _t'3 Vone; temp _tmp_buf (Vint (Int.repr 0));
           gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (nullval, (nullval, nullval))) octx; 
         ERR ep; data_at_ Tsh tp md; EVP_MD_NNnode dsh vals d;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ictx)).
  { clear H. 
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer2. apply data_at_valid_ptr; [intuition | omega ]. }
  { clear H. forward. 
    unfold EVP_MD_NNnode; Intros. rename H into TSH.
    destruct vals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
    forward. forward. entailer!. simpl. rewrite SZ2; trivial. 
    unfold EVP_MD_NNnode; entailer!. }
  { subst md; contradiction. }
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at_ Tsh tp md; EVP_MD_NNnode dsh vals d;
         EX m :_, (!!(malloc_compatible (Int.unsigned ctxsz) m) 
             && data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (m, (nullval, nullval))) octx * 
                data_at_ Tsh tp m);
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ictx));
  [ clear H | inv H | ].
  { forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at_ Tsh tp md; EVP_MD_NNnode dsh vals d;
         EX m :_, (!!(malloc_compatible (Int.unsigned ctxsz) m) 
             && data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (m, (nullval, nullval))) octx * 
                memory_block Tsh (Int.unsigned ctxsz) m);
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ictx));
    [ contradiction | clear H |].
    { forward. unfold EVP_MD_NNnode; Intros. rename H into TSH.
      destruct vals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
      forward.
      forward_call (Int.unsigned ctxsz). simpl; rewrite Int.repr_unsigned; apply prop_right; trivial.
      Intros m. forward. forward.
      apply semax_orp_SEPx; Intros.
      + (*m=Null*)
        subst; simpl.
        forward_if ( PROP (False) LOCAL () SEP ()).
        - clear H.
          forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                 ep, Vint (Int.repr 142)).
          forward. Exists nullval. entailer!. unfold MDCTXFinished, EVP_MD_NNnode.
          Exists nid ctxsz md tp; unfold EVP_MD_CTX_NNnode; entailer!.
          apply orp_right1. unfold MDCTXInitializedDigestSet. entailer!.
        - inv H.
        - intros. unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
          old_go_lower. clear H. destruct ek; simpl; normalize. 
      + (*m<>null*)
        rename H into M. 
        rewrite memory_block_isptr; Intros.
        rewrite eval_cast_neutral_isptr; simpl; trivial.
        forward_if (
          PROP ( )
          LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
          SEP (memory_block Tsh (Int.unsigned ctxsz) m;
               data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (m, (nullval, nullval))) octx; 
               ERR ep; data_at_ Tsh tp md;
               data_at dsh (Tstruct _env_md_st noattr) (tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) d;
               data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ictx)).
        - clear H.
          apply denote_tc_test_eq_split; [ apply sepcon_valid_pointer1 | apply valid_pointer_null].
          apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
          apply sepcon_valid_pointer1. apply memory_block_valid_ptr. intuition. omega.
        - destruct m; try contradiction. simpl in H. inv H.
        - clear H. forward. entailer!.
        - intros. unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
          old_go_lower. clear H. destruct ek; simpl; normalize. entailer!. 
          Exists m; unfold EVP_MD_NNnode; entailer!. }
    Intros m. rename H into M. forward. forward. forward.
    unfold EVP_MD_NNnode; Intros. rename H into TSH. 
    destruct vals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
    forward. 
    replace_SEP 1 (data_at Tsh tp (default_val tp) md) by entailer!.
    forward_call ((Tsh,Tsh),m, md, Int.unsigned ctxsz, Build_REPTYPE tp (default_val tp)).
         { rewrite Int.repr_unsigned; entailer!. }
         { simpl. cancel. }
         { simpl; split; trivial. intuition. split; trivial.
           split. apply Int.unsigned_range_2. rewrite SZ3; trivial. }
    entailer!. Exists m; unfold EVP_MD_NNnode; entailer!. }
  Intros m. rename H into M. forward. forward. forward. 
  forward_if (
    PROP ( )
    LOCAL (temp _t'5 (Vint (Int.repr 0)); gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at_ Tsh tp md; EVP_MD_NNnode dsh vals d;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (m, (nullval, Vint Int.zero))) octx;
         data_at_ Tsh tp m;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ictx)).
  { contradiction. }
  { clear H. forward. entailer!. }
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at_ Tsh tp md; EVP_MD_NNnode dsh vals d;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (m, (nullval, Vint Int.zero))) octx;
         data_at_ Tsh tp m;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (md, (nullval, nullval))) ictx)).
  { contradiction. }
  { clear H. forward. entailer!. }
  forward. Exists Vone; unfold MDCTXFinished; entailer!.
  Exists nid ctxsz md tp. unfold EVP_MD_CTX_NNnode; entailer!.
  apply orp_right2. Exists m tp; entailer!.
Time Qed.

(*Also supports Hashed octx, since Hashed octx |-- Finished octx. (BUT THAT'S NOT EXPOSED!
  Allocation is performed, and result may be Vone or Vnull*)
Definition EVP_MD_CTX_copy_ex_SPEC_Finished_NEQ := DECLARE _EVP_MD_CTX_copy_ex
  WITH ep: val, octx:val, ictx:val,
       nid:int, ctxsz:int, sh:share * share, vals:_, t:val,
       nid':int, ctxsz':int, d:val
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (get_ctxsize (snd vals) = Vint ctxsz' /\ get_type (snd vals) = Vint nid';
            get_ctxsize (fst vals) = Vint ctxsz; 4 <= Int.unsigned ctxsz <= Int.max_unsigned; d<>t)
      LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
      SEP (ERR ep; MDCTXFinished nid' ctxsz' d octx; 
           MDCTXFinished nid ctxsz t ictx;
           EVP_MD_NNnode (fst sh) (fst vals) t; EVP_MD_NNnode (snd sh) (snd vals) d)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERR ep; MDCTXFinished nid ctxsz t ictx; 
            EVP_MD_NNnode (fst sh) (fst vals) t; EVP_MD_NNnode (snd sh) (snd vals) d;
            (!!(rv=nullval) && MDCTXInitializedDigestSet t octx) 
            || (!!(rv=Vone) && MDCTXFinished nid ctxsz t octx)).

(*Also supports Hashed octx, since Hashed octx |-- Finished octx.
  No allocation is performed, and result value is always Vone*)
Definition EVP_MD_CTX_copy_ex_SPEC_Finished_EQ := DECLARE _EVP_MD_CTX_copy_ex
  WITH ep: val, octx:val, ictx:val,
       nid:int, ctxsz:int, tsh:share, vals:_, t:val
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (get_ctxsize vals = Vint ctxsz; 4 <= Int.unsigned ctxsz <= Int.max_unsigned)
      LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
      SEP (ERR ep; MDCTXFinished nid ctxsz t octx; 
           MDCTXFinished nid ctxsz t ictx;
           EVP_MD_NNnode tsh vals t)
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp Vone)
       SEP (ERR ep; MDCTXFinished nid ctxsz t ictx; EVP_MD_NNnode tsh vals t;
            MDCTXFinished nid ctxsz t octx).

Lemma body_EVP_MD_CTX_copy_ex_Finished_NEQ: semax_body Vprog Gprog_copy_ex f_EVP_MD_CTX_copy_ex EVP_MD_CTX_copy_ex_SPEC_Finished_NEQ.
Proof. 
  start_function. destruct H as [SZ' NID'].
  rename H0 into SZ. rename H1 into SZ1. rename H2 into DT. forward.
  rewrite MDCTXFinished_isptr' with (p:=ictx); Intros.
  rewrite MDCTXFinished_isptr' with (p:=octx); Intros.
  rewrite EVP_MD_NNnode_isptr' with (p:= t); Intros.
  rewrite EVP_MD_NNnode_isptr' with (p:= d); Intros.
  destruct sh as [tsh dsh]. destruct vals as [tvals dvals]; simpl in *.
  destruct tvals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
  freeze [0;1;4] FR1.
  forward_if (
    PROP ( )
     LOCAL (temp _t'1 Vzero; temp _tmp_buf (Vint (Int.repr 0));
            gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
     SEP (FRZL FR1; MDCTXFinished nid ctxsz t ictx;
          EVP_MD_NNnode tsh (*tvals*)(tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t)).
  { clear H; 
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer1. 
    apply sepcon_valid_pointer2. apply MDCTXFinished_valid_ptr. }
  { subst; contradiction. } 
  { clear H. unfold MDCTXFinished. unfold EVP_MD_CTX_NNnode. Intros md tp.
    unfold EVP_MD_NNnode; Intros.
    forward. forward. entailer!.
    + destruct t; try contradiction; simpl; trivial.
    + unfold MDCTXFinished, EVP_MD_NNnode, EVP_MD_CTX_NNnode. Exists md tp; entailer!. }
  forward_if (
    PROP ( )
    LOCAL (temp _tmp_buf (Vint (Int.repr 0));
           gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (FRZL FR1; MDCTXFinished nid ctxsz t ictx;
         EVP_MD_NNnode tsh (*tvals*)(tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t)).
  { elim H; trivial. }
  { clear H; forward; entailer!. }
  thaw FR1.
      unfold MDCTXFinished,EVP_MD_CTX_NNnode. Intros md' tp' md tp.
      rename H into SZ2'. rename H0 into TP'. rename H1 into SZ3'. (* rename H2 into V'.*)
      rename H2 into SZ2. rename H3 into TP. rename H4 into SZ3.
      rewrite data_at__isptr with (p:=md); Intros.
      rewrite data_at__isptr with (p:=md'); Intros.
      forward. forward.
      forward_if (
        PROP ( )
        LOCAL (temp _tmp_buf (Vint (Int.repr 0)); gvar ___stringlit_1 ep;
               temp _out octx; temp _in ictx)
        SEP (ERR ep;
             data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (md', (nullval, nullval))) octx;
             data_at_ Tsh tp' md'; EVP_MD_NNnode dsh dvals d;
             data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx;
             data_at_ Tsh tp md; EVP_MD_NNnode tsh (*tvals*)(tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t)).
      { clear H.
        apply denote_tc_test_eq_split; 
        [ apply sepcon_valid_pointer1 | apply sepcon_valid_pointer2; apply EVP_MD_NNnode_validptr ].
        apply sepcon_valid_pointer1; apply sepcon_valid_pointer1. apply sepcon_valid_pointer2; apply EVP_MD_NNnode_validptr. }
      { apply ptr_comp_Ceq_t in H; trivial; simpl in H. congruence. }
      { forward; entailer!. }
  gather_SEP 1 2.
  replace_SEP 0 (MDCTXConfigured nid' ctxsz' d octx || MDCTXFinished nid' ctxsz' d octx).
  { unfold MDCTXFinished; entailer!. apply orp_right2. Exists md' tp'; entailer!. }
  forward_call (octx, ClConfiguredOrFinished dsh dvals d).
  { simpl. Exists nid' ctxsz'; entailer!. }
  simpl. normalize.
  rewrite data_at__isptr with (p:=md); Intros.
  forward. simpl; unfold MDCTXInitialized; Intros. forward.
  simpl. rewrite sem_cast_neutral_ptr; simpl; trivial.
  forward. freeze [0;1;2] FR1.
  forward_if (
    PROP ( )
    LOCAL (temp _t'3 Vone; temp _tmp_buf nullval;
           gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (FRZL FR1;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx; 
         data_at_ Tsh tp md;
         EVP_MD_NNnode tsh (*tvals*)(tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t)).
  { clear H. 
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. apply data_at_valid_ptr; [intuition | omega ]. }
  { clear H. forward. 
    unfold EVP_MD_NNnode; Intros. rename H into TSH.
    (*destruct tvals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.*)
    forward. forward. unfold EVP_MD_NNnode; entailer!. simpl. rewrite SZ2; trivial. }
  { subst md; contradiction. }
  thaw FR1.
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (EVP_MD_NNnode dsh dvals d; ERR ep;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx;
         data_at_ Tsh tp md; EVP_MD_NNnode tsh (*tvals*)(tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t;
         EX m :_, (!!(malloc_compatible (Int.unsigned ctxsz) m) 
             && data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) octx * 
                data_at_ Tsh tp m)));
  [ clear H | inv H | ].
  { forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (EVP_MD_NNnode dsh dvals d; ERR ep;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx;
         data_at_ Tsh tp md; EVP_MD_NNnode tsh (*tvals*)(tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t;
         EX m :_, (!!(malloc_compatible (Int.unsigned ctxsz) m) 
             && data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) octx * 
                memory_block Tsh (Int.unsigned ctxsz) m))).
    { contradiction. }
    { clear H. forward. unfold EVP_MD_NNnode at 2; Intros. rename H into TSH.
      (*destruct tvals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.*)
      forward.
      forward_call (Int.unsigned ctxsz).
      { simpl; rewrite Int.repr_unsigned; entailer!. }
      Intros m; forward. forward.
      apply semax_orp_SEPx; Intros.
      + (*m=Null*)
        subst; simpl.
        forward_if ( PROP (False) LOCAL () SEP ()).
        - clear H.
          forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                 ep, Vint (Int.repr 142)).
          forward. Exists nullval. entailer!. unfold MDCTXFinished, EVP_MD_NNnode.
          Exists md tp; unfold EVP_MD_CTX_NNnode; entailer!.
          apply orp_right1. unfold MDCTXInitializedDigestSet. entailer!.
        - inv H.
        - intros. unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
          old_go_lower. clear H. destruct ek; simpl; normalize. 
      + (*m<>null*)
        rename H into M. 
        rewrite memory_block_isptr; Intros.
        rewrite sem_cast_neutral_ptr; simpl; trivial.
        forward_if (
          PROP ( )
          LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
          SEP (memory_block Tsh (Int.unsigned ctxsz) m;
               data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) octx; 
               ERR ep; data_at_ Tsh tp md; EVP_MD_NNnode dsh dvals d;
               data_at tsh (Tstruct _env_md_st noattr) (tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t;
               data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx)).
        - clear H.
          apply denote_tc_test_eq_split; [ apply sepcon_valid_pointer1 | apply valid_pointer_null].
          apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
          apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply memory_block_valid_ptr. intuition. omega.
        - destruct m; try contradiction. simpl in H. inv H.
        - clear H. forward. entailer!.
        - intros. unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
          old_go_lower. clear H. destruct ek; simpl; normalize. entailer!.
          Exists m; entailer!. unfold EVP_MD_NNnode; entailer!. }
    Intros m. rename H into M. forward. forward. forward.
    unfold EVP_MD_NNnode; Intros. rename H into TSH. 
    (*destruct tvals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.*)
    forward.
(*    replace_SEP 1 (data_at Tsh tp (default_val tp) md) by entailer!.*)
    replace_SEP 3 (data_at Tsh tp (default_val tp) md) by entailer!.
    forward_call ((Tsh,Tsh),m, md, Int.unsigned ctxsz, Build_REPTYPE tp (default_val tp)).
         { rewrite Int.repr_unsigned. simpl. apply prop_right; trivial. }
         { simpl. cancel. }
         { simpl in *; split; trivial. intuition. split; trivial.
           split. apply Int.unsigned_range_2. rewrite SZ3; trivial. }
    go_lower. normalize. Exists m; unfold EVP_MD_NNnode; normalize.
    apply andp_right; [ apply prop_right; repeat split; trivial | cancel]. }
  Intros m. rename H into M. forward. forward. forward. 
  forward_if (
    PROP ( )
    LOCAL (temp _t'5 (Vint (Int.repr 0)); gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (EVP_MD_NNnode dsh dvals d; ERR ep;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx;
         data_at_ Tsh tp md; EVP_MD_NNnode tsh (*tvals*)(tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, Vint Int.zero))) octx; 
         data_at_ Tsh tp m)).
  { contradiction. }
  { clear H. forward. entailer!. }
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (EVP_MD_NNnode dsh dvals d; ERR ep;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx;
         data_at_ Tsh tp md; EVP_MD_NNnode tsh (*tvals*)(tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, Vint Int.zero))) octx; 
         data_at_ Tsh tp m)).
  { contradiction. }
  { clear H. forward. entailer!. }
  forward. Exists Vone; unfold MDCTXFinished; entailer!.
  Exists md tp. unfold EVP_MD_CTX_NNnode; entailer!.
  apply orp_right2. Exists m tp; entailer!.
Time Qed.

Lemma body_EVP_MD_CTX_copy_ex_FinishedEQ: semax_body Vprog Gprog_copy_ex f_EVP_MD_CTX_copy_ex EVP_MD_CTX_copy_ex_SPEC_Finished_EQ.
Proof. 
  start_function. rename H into SZ. rename H0 into SZ1. forward.
  rewrite MDCTXFinished_isptr' with (p:=ictx); Intros.
  rewrite MDCTXFinished_isptr' with (p:=octx); Intros.
  rewrite EVP_MD_NNnode_isptr'; Intros.
  forward_if (
    PROP ( )
     LOCAL (temp _t'1 Vzero; temp _tmp_buf (Vint (Int.repr 0));
            gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
     SEP (ERR ep; MDCTXFinished nid ctxsz t octx; MDCTXFinished nid ctxsz t ictx; EVP_MD_NNnode tsh vals t)).
  { clear H; 
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. apply MDCTXFinished_valid_ptr. }
  { subst; contradiction. } 
  { clear H. unfold MDCTXFinished, EVP_MD_CTX_NNnode. Intros md' tp' md tp.
    unfold EVP_MD_NNnode; Intros.
    forward. forward. entailer!.
    + destruct t; try contradiction; simpl; trivial.
    + unfold MDCTXFinished, EVP_MD_NNnode, EVP_MD_CTX_NNnode.
      Exists md' tp' md tp; entailer!. }
  forward_if (
    PROP ( )
    LOCAL (temp _tmp_buf (Vint (Int.repr 0));
           gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; MDCTXFinished nid ctxsz t octx; MDCTXFinished nid ctxsz t ictx;
         EVP_MD_NNnode tsh vals t)).
  { elim H; trivial. }
  { clear H; forward; entailer!. }
  unfold MDCTXFinished, EVP_MD_CTX_NNnode. Intros md' tp' md tp.
  rewrite H0 in H2; inv H2. clear H3.
  rename H into SZ2. rename H0 into HTP. rename H1 into SZ3.
  rewrite data_at__isptr with (p:=md); Intros.
  rewrite data_at__isptr with (p:=md'); Intros.
  forward. forward.
  forward_if (
    PROP ( )
    LOCAL (temp _tmp_buf md'; gvar ___stringlit_1 ep;
           temp _out octx; temp _in ictx)
    SEP (ERR ep; EVP_MD_NNnode tsh vals t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (nullval, (nullval, nullval))) octx;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx;
         data_at_ Tsh tp md; data_at_ Tsh tp md')).
  { clear H.
    apply denote_tc_test_eq_split; 
    apply sepcon_valid_pointer2; apply EVP_MD_NNnode_validptr. }
  { clear H. forward. forward. entailer!. }
  { apply ptr_comp_Ceq_f in H; trivial; simpl in H. elim H; trivial. }
  forward_call (octx, ClInitializedDigestSet t tsh vals).
  { simpl. Exists ctxsz; unfold MDCTXInitializedDigestSet; entailer!. }
  forward. simpl; unfold MDCTXInitialized; Intros. forward.
  simpl. rewrite sem_cast_neutral_ptr; simpl; trivial.
  forward.
  forward_if (
    PROP ( )
    LOCAL (temp _t'3 Vone; temp _tmp_buf md';
           gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (nullval, (nullval, nullval))) octx; 
         ERR ep; data_at_ Tsh tp md; EVP_MD_NNnode tsh vals t; data_at_ Tsh tp md';
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx)).
  { clear H. 
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. apply data_at_valid_ptr; [intuition | omega ]. }
  { clear H. forward. 
    unfold EVP_MD_NNnode; Intros. rename H into TSH.
    destruct vals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
    forward. forward. unfold EVP_MD_NNnode; entailer!. simpl. rewrite SZ2; trivial. }
  { subst md; contradiction. }
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at_ Tsh tp md; EVP_MD_NNnode tsh vals t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md', (nullval, nullval))) octx;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx; 
         data_at_ Tsh tp md'));
  [ clear H | inv H | ].
  { forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at_ Tsh tp md; EVP_MD_NNnode tsh vals t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md', (nullval, nullval))) octx;
         data_at_ Tsh tp md';
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx)).
    { clear H. apply denote_tc_test_eq_split; [ apply sepcon_valid_pointer1 | apply valid_pointer_null].
      apply sepcon_valid_pointer2; apply data_at_valid_ptr; intuition. }
    { clear H. forward. entailer!. cancel. } 
    { subst; contradiction. }
    forward. forward. forward. 
    unfold EVP_MD_NNnode; Intros. rename H into TSH.
    destruct vals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
    forward.
    replace_SEP 4 (memory_block Tsh (Int.unsigned ctxsz) md').
    { rewrite <- SZ3. entailer!. 
      eapply derives_trans; [ apply data_at_memory_block | cancel]. }
    replace_SEP 1 (data_at Tsh tp (default_val tp) md) by entailer!.
    forward_call ((Tsh,Tsh),md', md, Int.unsigned ctxsz, Build_REPTYPE tp (default_val tp)).
         { rewrite Int.repr_unsigned. simpl. apply prop_right; trivial. }
         { simpl. cancel. }
         { simpl in *; split; trivial. intuition. split; trivial.
           split. apply Int.unsigned_range_2. rewrite SZ3; trivial. }
    entailer!. unfold EVP_MD_NNnode; entailer!. }

  forward. forward. forward. 
  forward_if (
    PROP ( )
    LOCAL (temp _t'5 (Vint (Int.repr 0)); gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at_ Tsh tp md; EVP_MD_NNnode tsh vals t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md', (nullval, Vint Int.zero))) octx;
         data_at_ Tsh tp md';
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx)).
  { contradiction. }
  { clear H. forward. entailer!. }
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at_ Tsh tp md; EVP_MD_NNnode tsh vals t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md', (nullval, Vint Int.zero))) octx;
         data_at_ Tsh tp md';
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx)).
  { contradiction. }
  { clear H. forward. entailer!. }
  forward. cancel. unfold MDCTXFinished, EVP_MD_CTX_NNnode.
  Exists md md' tp tp; entailer!.
Time Qed.

(*Also supports Hashed octx, since Hashed octx |-- Finished octx.
  Allocation is performed, and result may be Vone or Vnull*)
Definition EVP_MD_CTX_copy_ex_SPEC_Hashed_NEQ := DECLARE _EVP_MD_CTX_copy_ex
  WITH ep: val, octx:val, ictx:val,
       nid:int, ctxsz:int , data:list int, sh:share * share, vals:_, t:val,
       nid':int, ctxsz':int, d:val
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (get_ctxsize (snd vals) = Vint ctxsz' /\ get_type (snd vals) = Vint nid';
            get_ctxsize (fst vals) = Vint ctxsz; 4 <= Int.unsigned ctxsz <= Int.max_unsigned; d<>t)
      LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
      SEP (ERR ep; MDCTXFinished nid' ctxsz' d octx; 
           MDCTXHashed nid ctxsz (map Int.unsigned data) t ictx;
           EVP_MD_NNnode (fst sh) (fst vals) t; EVP_MD_NNnode (snd sh) (snd vals) d)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERR ep; MDCTXHashed nid ctxsz (map Int.unsigned data) t ictx; 
            EVP_MD_NNnode (fst sh) (fst vals) t; EVP_MD_NNnode (snd sh) (snd vals) d;
            (!!(rv=nullval) && MDCTXInitializedDigestSet t octx) 
            || (!!(rv=Vone) && MDCTXHashed nid ctxsz (map Int.unsigned data) t octx)).

(*Also supports Hashed octx, since Hashed octx |-- Finished octx.
  No allocation is performed, and result value is always Vone*)
Definition EVP_MD_CTX_copy_ex_SPEC_Hashed_EQ := DECLARE _EVP_MD_CTX_copy_ex
  WITH ep: val, octx:val, ictx:val,
       nid:int, ctxsz:int, data:list int, tsh:share, vals:_, t:val
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (get_ctxsize vals = Vint ctxsz; 4 <= Int.unsigned ctxsz <= Int.max_unsigned)
      LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
      SEP (ERR ep; MDCTXFinished nid ctxsz t octx; 
           MDCTXHashed nid ctxsz (map Int.unsigned data) t ictx;
           EVP_MD_NNnode tsh vals t)
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp Vone)
       SEP (ERR ep; MDCTXHashed nid ctxsz (map Int.unsigned data) t ictx; EVP_MD_NNnode tsh vals t;
            MDCTXHashed nid ctxsz (map Int.unsigned data) t octx).


Lemma body_EVP_MD_CTX_copy_ex_Hashed_NEQ: semax_body Vprog Gprog_copy_ex f_EVP_MD_CTX_copy_ex EVP_MD_CTX_copy_ex_SPEC_Hashed_NEQ.
Proof. 
  start_function. destruct H as [SZ' NID'].
  rename H0 into SZ. rename H1 into SZ1. rename H2 into DT. forward.
  rewrite MDCTXHashed_isptr'; Intros.
  rewrite MDCTXFinished_isptr'; Intros.
  rewrite EVP_MD_NNnode_isptr' with (p:= t); Intros.
  rewrite EVP_MD_NNnode_isptr' with (p:= d); Intros.
  destruct sh as [tsh dsh]. destruct vals as [tvals dvals]; simpl in *.
  destruct tvals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
  freeze [0;1;4] FR1.
  forward_if (
    PROP ( )
     LOCAL (temp _t'1 Vzero; temp _tmp_buf (Vint (Int.repr 0));
            gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
     SEP (FRZL FR1; MDCTXHashed nid ctxsz (map Int.unsigned data) t ictx;
          EVP_MD_NNnode tsh (*tvals*)(tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t)).
  { clear H; 
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer1. 
    apply sepcon_valid_pointer2. apply MDCTXHashed_valid_ptr. }
  { subst; contradiction. } 
  { clear H. unfold MDCTXHashed. unfold EVP_MD_CTX_NNnode. Intros md tp v.
    unfold EVP_MD_NNnode; Intros.
    forward. forward. entailer!.
    + destruct t; try contradiction; simpl; trivial.
    + unfold MDCTXHashed, EVP_MD_NNnode, EVP_MD_CTX_NNnode. Exists md tp v; entailer!. }
  forward_if (
    PROP ( )
    LOCAL (temp _tmp_buf (Vint (Int.repr 0));
           gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (FRZL FR1; MDCTXHashed nid ctxsz (map Int.unsigned data) t ictx;
         EVP_MD_NNnode tsh (*tvals*)(tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t)).
  { elim H; trivial. }
  { clear H; forward; entailer!. }
  thaw FR1.
      unfold MDCTXFinished, MDCTXHashed, EVP_MD_CTX_NNnode. Intros md' tp' md tp v.
      rename H into SZ2'. rename H0 into TP'. rename H1 into SZ3'. (* rename H2 into V'.*)
      rename H2 into SZ2. rename H3 into TP. rename H4 into SZ3. rename H5 into V.
      rewrite data_at_isptr with (p:=md); Intros.
      rewrite data_at__isptr with (p:=md'); Intros.
      forward. forward.
      forward_if (
        PROP ( )
        LOCAL (temp _tmp_buf (Vint (Int.repr 0)); gvar ___stringlit_1 ep;
               temp _out octx; temp _in ictx)
        SEP (ERR ep;
             data_at Tsh (Tstruct _env_md_ctx_st noattr) (d, (md', (nullval, nullval))) octx;
             data_at_ Tsh tp' md'; EVP_MD_NNnode dsh dvals d;
             data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx;
             data_at Tsh tp v md; EVP_MD_NNnode tsh (*tvals*)(tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t)).
      { clear H.
        apply denote_tc_test_eq_split; 
        [ apply sepcon_valid_pointer1 | apply sepcon_valid_pointer2; apply EVP_MD_NNnode_validptr ].
        apply sepcon_valid_pointer1; apply sepcon_valid_pointer1. apply sepcon_valid_pointer2; apply EVP_MD_NNnode_validptr. }
      { apply ptr_comp_Ceq_t in H; trivial; simpl in H. congruence. }
      { forward; entailer!. }
  gather_SEP 1 2.
  replace_SEP 0 (MDCTXConfigured nid' ctxsz' d octx || MDCTXFinished nid' ctxsz' d octx).
  { unfold MDCTXFinished; entailer!. apply orp_right2. Exists md' tp'; entailer!. }
  forward_call (octx, ClConfiguredOrFinished dsh dvals d).
  { simpl. Exists nid' ctxsz'; entailer!. }
  simpl. normalize.
  rewrite data_at_isptr with (p:=md); Intros.
  forward. simpl; unfold MDCTXInitialized; Intros. forward.
  simpl. rewrite sem_cast_neutral_ptr; simpl; trivial.
  forward. freeze [0;1;2] FR1.
  forward_if (
    PROP ( )
    LOCAL (temp _t'3 Vone; temp _tmp_buf nullval;
           gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (FRZL FR1;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx; data_at Tsh tp v md;
         EVP_MD_NNnode tsh (*tvals*)(tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t)).
  { clear H. 
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. apply data_at_valid_ptr; [intuition | omega ]. }
  { clear H. forward. 
    unfold EVP_MD_NNnode; Intros. rename H into TSH.
    (*destruct tvals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.*)
    forward. forward. unfold EVP_MD_NNnode; entailer!. simpl. rewrite SZ2; trivial. }
  { subst md; contradiction. }
  thaw FR1.
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (EVP_MD_NNnode dsh dvals d; ERR ep;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx;
         data_at Tsh tp v md; EVP_MD_NNnode tsh (*tvals*)(tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t;
         EX m :_, (!!(malloc_compatible (Int.unsigned ctxsz) m) 
             && data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) octx * 
                data_at Tsh tp v m)));
  [ clear H | inv H | ].
  { forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (EVP_MD_NNnode dsh dvals d; ERR ep;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx;
         data_at Tsh tp v md; EVP_MD_NNnode tsh (*tvals*)(tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t;
         EX m :_, (!!(malloc_compatible (Int.unsigned ctxsz) m) 
             && data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) octx * 
                memory_block Tsh (Int.unsigned ctxsz) m))).
    { contradiction. }
    { clear H. forward. unfold EVP_MD_NNnode at 2; Intros. rename H into TSH.
      (*destruct tvals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.*)
      forward.
      forward_call (Int.unsigned ctxsz).
      { simpl; rewrite Int.repr_unsigned; entailer!. }
      Intros m; forward. forward.
      apply semax_orp_SEPx; Intros.
      + (*m=Null*)
        subst; simpl.
        forward_if ( PROP (False) LOCAL () SEP ()).
        - clear H.
          forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                 ep, Vint (Int.repr 142)).
          forward. Exists nullval. entailer!. unfold MDCTXHashed, EVP_MD_NNnode.
          Exists md tp; unfold EVP_MD_CTX_NNnode; entailer!.
          Exists v. entailer!. 
          apply orp_right1. unfold MDCTXInitializedDigestSet. entailer!.
        - inv H.
        - intros. unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
          old_go_lower. clear H. destruct ek; simpl; normalize. 
      + (*m<>null*)
        rename H into M. 
        rewrite memory_block_isptr; Intros.
        rewrite sem_cast_neutral_ptr; simpl; trivial.
        forward_if (
          PROP ( )
          LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
          SEP (memory_block Tsh (Int.unsigned ctxsz) m;
               data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) octx; 
               ERR ep; data_at Tsh tp v md; EVP_MD_NNnode dsh dvals d;
               data_at tsh (Tstruct _env_md_st noattr) (tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t;
               data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx)).
        - clear H.
          apply denote_tc_test_eq_split; [ apply sepcon_valid_pointer1 | apply valid_pointer_null].
          apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
          apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply memory_block_valid_ptr. intuition. omega.
        - destruct m; try contradiction. simpl in H. inv H.
        - clear H. forward. entailer!.
        - intros. unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
          old_go_lower. clear H. destruct ek; simpl; normalize. entailer!.
          Exists m; entailer!. unfold EVP_MD_NNnode; entailer!. }
    Intros m. rename H into M. forward. forward. forward.
    unfold EVP_MD_NNnode; Intros. rename H into TSH. 
    (*destruct tvals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.*)
    forward. 
(*    replace_SEP 1 (data_at Tsh tp (default_val tp) md) by entailer!.*)
    forward_call ((Tsh,Tsh),m, md, Int.unsigned ctxsz, Build_REPTYPE tp v).
         { rewrite Int.repr_unsigned. simpl. apply prop_right; trivial. }
         { simpl. cancel. }
         { simpl in *; split; trivial. intuition. split; trivial.
           split. apply Int.unsigned_range_2. rewrite SZ3; trivial. }
    go_lower. normalize. Exists m; unfold EVP_MD_NNnode; normalize.
    apply andp_right; [ apply prop_right; repeat split; trivial | cancel]. }
  Intros m. rename H into M. forward. forward. forward. 
  forward_if (
    PROP ( )
    LOCAL (temp _t'5 (Vint (Int.repr 0)); gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (EVP_MD_NNnode dsh dvals d; ERR ep;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx;
         data_at Tsh tp v md; EVP_MD_NNnode tsh (*tvals*)(tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, Vint Int.zero))) octx; 
         data_at Tsh tp v m)).
  { contradiction. }
  { clear H. forward. entailer!. }
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (EVP_MD_NNnode dsh dvals d; ERR ep;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx;
         data_at Tsh tp v md; EVP_MD_NNnode tsh (*tvals*)(tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, Vint Int.zero))) octx; 
         data_at Tsh tp v m)).
  { contradiction. }
  { clear H. forward. entailer!. }
  forward. Exists Vone; unfold MDCTXHashed; entailer!.
  Exists md tp v. unfold EVP_MD_CTX_NNnode; entailer!.
  apply orp_right2. Exists m tp v; entailer!.
Time Qed.

Lemma body_EVP_MD_CTX_copy_ex_HashedEQ: semax_body Vprog Gprog_copy_ex f_EVP_MD_CTX_copy_ex EVP_MD_CTX_copy_ex_SPEC_Hashed_EQ.
Proof. 
  start_function. rename H into SZ. rename H0 into SZ1. forward.
  rewrite MDCTXHashed_isptr' with (p:=ictx); Intros.
  rewrite MDCTXFinished_isptr' with (p:=octx); Intros.
  rewrite EVP_MD_NNnode_isptr'; Intros.
  forward_if (
    PROP ( )
     LOCAL (temp _t'1 Vzero; temp _tmp_buf (Vint (Int.repr 0));
            gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
     SEP (ERR ep; MDCTXFinished nid ctxsz t octx; MDCTXHashed nid ctxsz (map Int.unsigned data) t ictx; EVP_MD_NNnode tsh vals t)).
  { clear H; 
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. apply MDCTXHashed_valid_ptr. }
  { subst; contradiction. } 
  { clear H. unfold MDCTXHashed, EVP_MD_CTX_NNnode. Intros md tp v.
    unfold EVP_MD_NNnode; Intros.
    forward. forward. entailer!.
    + destruct t; try contradiction; simpl; trivial.
    + unfold MDCTXHashed, EVP_MD_NNnode, EVP_MD_CTX_NNnode. Exists md tp v; entailer!. }
  forward_if (
    PROP ( )
    LOCAL (temp _tmp_buf (Vint (Int.repr 0));
           gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; MDCTXFinished nid ctxsz t octx; MDCTXHashed nid ctxsz (map Int.unsigned data) t ictx;
         EVP_MD_NNnode tsh vals t)).
  { elim H; trivial. }
  { clear H; forward; entailer!. }
  unfold MDCTXFinished, MDCTXHashed, EVP_MD_CTX_NNnode. Intros md' tp' md tp v.
  rewrite H0 in H2; inv H2. clear H3. rename H4 into V.
  rename H into SZ2. rename H0 into HTP. rename H1 into SZ3.
  rewrite data_at_isptr with (p:=md); Intros.
  rewrite data_at__isptr with (p:=md'); Intros.
  forward. forward.
  forward_if (
    PROP ( )
    LOCAL (temp _tmp_buf md'; gvar ___stringlit_1 ep;
           temp _out octx; temp _in ictx)
    SEP (ERR ep; EVP_MD_NNnode tsh vals t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (nullval, (nullval, nullval))) octx;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx;
         data_at Tsh tp v md; data_at_ Tsh tp md')).
  { clear H.
    apply denote_tc_test_eq_split; 
    apply sepcon_valid_pointer2; apply EVP_MD_NNnode_validptr. }
  { clear H. forward. forward. entailer!. }
  { apply ptr_comp_Ceq_f in H; trivial; simpl in H. elim H; trivial. }
  forward_call (octx, ClInitializedDigestSet t tsh vals).
  { simpl. Exists ctxsz; unfold MDCTXInitializedDigestSet; entailer!. }
  forward. simpl; unfold MDCTXInitialized; Intros. forward.
  simpl. rewrite sem_cast_neutral_ptr; simpl; trivial.
  forward.
  forward_if (
    PROP ( )
    LOCAL (temp _t'3 Vone; temp _tmp_buf md';
           gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (nullval, (nullval, nullval))) octx; 
         ERR ep; data_at Tsh tp v md; EVP_MD_NNnode tsh vals t; data_at_ Tsh tp md';
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx)).
  { clear H. 
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. apply data_at_valid_ptr; [intuition | omega ]. }
  { clear H. forward. 
    unfold EVP_MD_NNnode; Intros. rename H into TSH.
    destruct vals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
    forward. forward. unfold EVP_MD_NNnode; entailer!. simpl. rewrite SZ2; trivial. }
  { subst md; contradiction. }
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at Tsh tp v md; EVP_MD_NNnode tsh vals t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md', (nullval, nullval))) octx;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx; 
         data_at Tsh tp v md'));
  [ clear H | inv H | ].
  { forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at Tsh tp v md; EVP_MD_NNnode tsh vals t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md', (nullval, nullval))) octx;
         data_at_ Tsh tp md';
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx)).
    { clear H. apply denote_tc_test_eq_split; [ apply sepcon_valid_pointer1 | apply valid_pointer_null].
      apply sepcon_valid_pointer2; apply data_at_valid_ptr; intuition. }
    { clear H. forward. entailer!. cancel. } 
    { subst; contradiction. }
    forward. forward. forward. 
    unfold EVP_MD_NNnode; Intros. rename H into TSH.
    destruct vals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
    forward.
    replace_SEP 4 (memory_block Tsh (Int.unsigned ctxsz) md').
    { rewrite <- SZ3. entailer!. 
      eapply derives_trans; [ apply data_at_memory_block | cancel]. }
    forward_call ((Tsh,Tsh),md', md,Int.unsigned ctxsz, Build_REPTYPE tp v). 
         { rewrite Int.repr_unsigned; entailer!. }
         { simpl. cancel. }
         { simpl; split; trivial. intuition. split; trivial. 
           split. apply Int.unsigned_range_2. rewrite SZ3; trivial. }
    entailer!. unfold EVP_MD_NNnode; entailer!. }

  forward. forward. forward. 
  forward_if (
    PROP ( )
    LOCAL (temp _t'5 (Vint (Int.repr 0)); gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at Tsh tp v md; EVP_MD_NNnode tsh vals t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md', (nullval, Vint Int.zero))) octx;
         data_at Tsh tp v md';
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx)).
  { contradiction. }
  { clear H. forward. entailer!. }
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at Tsh tp v md; EVP_MD_NNnode tsh vals t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md', (nullval, Vint Int.zero))) octx;
         data_at Tsh tp v md';
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx)).
  { contradiction. }
  { clear H. forward. entailer!. }
  forward. cancel. unfold MDCTXHashed, EVP_MD_CTX_NNnode.
  Exists md md' tp v tp v; entailer!.
Time Qed.

End EVP_MD_CTX_Protocol.

(*
(*Raises PUTERROR, even before octx is inspected. It's odd that we're not allowed to copy initialized digests...*)
Definition EVP_MD_CTX_copy_ex_SPEC_Initialized := DECLARE _EVP_MD_CTX_copy_ex
  WITH ep: val, octx:val, ictx:val
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP ()
      LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
      SEP (ERR ep;(*MDCTXInitialized octx;*) MDCTXInitialized ictx)
  POST [ tint] 
       PROP ()
       LOCAL (temp ret_temp nullval)
       SEP (ERR ep; (*MDCTXInitialized octx;*) MDCTXInitialized ictx).

Definition EVP_MD_CTX_copy_ex_SPEC_Hashed2 := DECLARE _EVP_MD_CTX_copy_ex
  WITH ep: val, octx:val, ictx:val,
       nid:int, ctxsz:int, data:list int, data':list int, tsh:share, vals:_, t:val
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (get_ctxsize vals = Vint ctxsz; 4 <= Int.unsigned ctxsz <= Int.max_unsigned)
      LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
      SEP (ERR ep; MDCTXHashed nid ctxsz (map Int.unsigned data') t octx; 
           MDCTXHashed nid ctxsz (map Int.unsigned data) t ictx;
           EVP_MD_NNnode tsh vals t)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERR ep; MDCTXHashed nid ctxsz (map Int.unsigned data) t ictx; EVP_MD_NNnode tsh vals t;
            (!!(rv=nullval) && MDCTXInitializedDigestSet t octx) 
            || (!!(rv=Vone) && MDCTXHashed nid ctxsz (map Int.unsigned data) t octx)(*; copyExPost case ictx octx rv*)).

Definition EVP_MD_CTX_copy_ex_SPEC_Finished := DECLARE _EVP_MD_CTX_copy_ex
  WITH ep: val, octx:val, ictx:val,
       nid:int, ctxsz:int, tsh:share, vals:_, t:val
  PRE [ _out OF (tptr (Tstruct _env_md_ctx_st noattr)),
        _in OF (tptr (Tstruct _env_md_ctx_st noattr)) ]
      PROP (get_ctxsize vals = Vint ctxsz; 4 <= Int.unsigned ctxsz <= Int.max_unsigned)
      LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
      SEP (ERR ep;MDCTXInitialized octx; MDCTXFinished nid ctxsz t ictx;
           EVP_MD_NNnode tsh vals t)
  POST [ tint] EX rv:_,
       PROP ()
       LOCAL (temp ret_temp rv)
       SEP (ERR ep; MDCTXFinished nid ctxsz t ictx; EVP_MD_NNnode tsh vals t;
            (!!(rv=nullval) && MDCTXInitializedDigestSet t octx) 
            || (!!(rv=Vone) && MDCTXFinished nid ctxsz t octx)).

Lemma body_EVP_MD_CTX_copy_exI: semax_body Vprog Gprog_copy_ex f_EVP_MD_CTX_copy_ex EVP_MD_CTX_copy_ex_SPEC_Initialized.
Proof. 
  start_function. forward.
  rewrite MDCTXInitialized_isptr' with (p:=ictx); Intros.
  (*  rewrite MDCTXInitialized_isptr' with (p:=octx); Intros.*)
  forward_if (
    PROP ( )
     LOCAL (temp _t'1 Vone; temp _tmp_buf (Vint (Int.repr 0));
            gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
     SEP (ERR ep; (*MDCTXInitialized octx;*) MDCTXInitialized ictx)).
  { clear H; 
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer2. apply MDCTXInitialized_valid_ptr. }
  { subst; contradiction. } 
  { unfold MDCTXInitialized. forward. forward. entailer!. }
  forward_if (PROP (False) LOCAL () SEP ()).
  { forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.repr 100),
                 ep, Vint (Int.repr 121)).
    forward.  }
  { inv H. }
  normalize.
Qed.

Lemma body_EVP_MD_CTX_copy_exH: semax_body Vprog Gprog_copy_ex f_EVP_MD_CTX_copy_ex EVP_MD_CTX_copy_ex_SPEC_Hashed.
Proof. 
  start_function. rename H into SZ. rename H0 into SZ1. forward.
  rewrite MDCTXInitialized_isptr'; Intros.
  rewrite MDCTXHashed_isptr'; Intros.
  rewrite EVP_MD_NNnode_isptr'; Intros.
  forward_if (
    PROP ( )
     LOCAL (temp _t'1 Vzero; temp _tmp_buf (Vint (Int.repr 0));
            gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
     SEP (ERR ep; MDCTXInitialized octx; MDCTXHashed nid ctxsz (map Int.unsigned data) t ictx; EVP_MD_NNnode tsh vals t)).
  { clear H; 
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. apply MDCTXHashed_valid_ptr. }
  { subst; contradiction. } 
  { unfold MDCTXHashed, EVP_MD_CTX_NNnode. Intros md tp v.
    unfold EVP_MD_NNnode; Intros.
    forward. forward. entailer!.
    + destruct t; try contradiction; simpl; trivial.
    + unfold MDCTXHashed, EVP_MD_NNnode, EVP_MD_CTX_NNnode. Exists md tp v; entailer!. }
  forward_if (
    PROP ( )
    LOCAL (temp _tmp_buf (Vint (Int.repr 0));
           gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; MDCTXInitialized octx; MDCTXHashed nid ctxsz (map Int.unsigned data) t ictx;
         EVP_MD_NNnode tsh vals t)).
  { elim H; trivial. }
  { clear H; forward; entailer!. }
  unfold MDCTXInitialized. forward.
  unfold MDCTXHashed, EVP_MD_CTX_NNnode; Intros md tp v.
  rename H into SZ2. rename H0 into HTP. rename H1 into SZ3. rename H2 into V.
  rewrite data_at_isptr with (p:=md); Intros.
  forward.
  forward_if (
    PROP ( )
    LOCAL (temp _tmp_buf (Vint (Int.repr 0)); gvar ___stringlit_1 ep;
           temp _out octx; temp _in ictx)
    SEP (ERR ep; EVP_MD_NNnode tsh vals t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (nullval, (nullval, (nullval, nullval))) octx;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx;
         data_at Tsh tp v md)).
  { clear H.
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer2. apply EVP_MD_NNnode_validptr. }
  { apply ptr_comp_Ceq_t in H; simpl; trivial; subst; contradiction. }
  { clear H. forward; entailer!. }
  forward_call (octx, ClInitialized).
  { simpl; unfold MDCTXInitialized; entailer!. }
  forward. simpl; unfold MDCTXInitialized. forward.
  simpl. rewrite sem_cast_neutral_ptr; simpl; trivial.
  forward.
  forward_if (
    PROP ( )
    LOCAL (temp _t'3 Vone; temp _tmp_buf (Vint (Int.repr 0));
           gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (nullval, (nullval, nullval))) octx; 
         ERR ep; data_at Tsh tp v md; EVP_MD_NNnode tsh vals t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx)).
  { clear H. 
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer2. apply data_at_valid_ptr; [intuition | omega ]. }
  { clear H. forward. 
    unfold EVP_MD_NNnode; Intros. rename H into TSH.
    destruct vals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
    forward. forward. entailer!. simpl. rewrite SZ2; trivial. 
    unfold EVP_MD_NNnode; entailer!. }
  { subst md; contradiction. }
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at Tsh tp v md; EVP_MD_NNnode tsh vals t;
         EX m :_, (!!(malloc_compatible (Int.unsigned ctxsz) m) 
             && data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) octx * 
                data_at Tsh tp v m);
         data_at Tsh (Tstruct _env_md_ctx_st noattr)
            (t, (md, (nullval, nullval))) ictx));
  [ clear H | inv H | ].
  { forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at Tsh tp v md; EVP_MD_NNnode tsh vals t;
         EX m :_, (!!(malloc_compatible (Int.unsigned ctxsz) m) 
             && data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) octx * 
                memory_block Tsh (Int.unsigned ctxsz) m);
         data_at Tsh (Tstruct _env_md_ctx_st noattr)
            (t, (md, (nullval, nullval))) ictx));
    [ contradiction | clear H |].
    { forward. unfold EVP_MD_NNnode; Intros. rename H into TSH.
      destruct vals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
      forward.
      forward_call (Int.unsigned ctxsz). simpl; rewrite Int.repr_unsigned; apply prop_right; trivial.
      Intros m. forward. forward.
      apply semax_orp_SEPx; Intros.
      + (*m=Null*)
        subst; simpl.
        forward_if ( PROP (False) LOCAL () SEP ()).
        - clear H.
          forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                 ep, Vint (Int.repr 142)).
          forward. Exists nullval. entailer!. unfold MDCTXHashed, EVP_MD_NNnode.
          Exists md tp v; unfold EVP_MD_CTX_NNnode; entailer!.
          apply orp_right1. unfold MDCTXInitializedDigestSet. cancel.
        - inv H.
        - intros. unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
          old_go_lower. clear H. destruct ek; simpl; normalize. 
      + (*m<>null*)
        rename H into M. 
        rewrite memory_block_isptr; Intros.
        rewrite eval_cast_neutral_isptr; simpl; trivial.
        forward_if (
          PROP ( )
          LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
          SEP (memory_block Tsh (Int.unsigned ctxsz) m;
               data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) octx; 
               ERR ep; data_at Tsh tp v md;
               data_at tsh (Tstruct _env_md_st noattr) (tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t;
               data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx)).
        - clear H.
          apply denote_tc_test_eq_split; [ apply sepcon_valid_pointer1 | apply valid_pointer_null].
          apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
          apply sepcon_valid_pointer1. apply memory_block_valid_ptr. intuition. omega.
        - destruct m; try contradiction. simpl in H. inv H.
        - clear H. forward. entailer!.
        - intros. unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
          old_go_lower. clear H. destruct ek; simpl; normalize. entailer!. 
          Exists m; unfold EVP_MD_NNnode; entailer!. }
    Intros m. rename H into M. forward. forward. forward.
    unfold EVP_MD_NNnode; Intros. rename H into TSH. 
    destruct vals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
    forward. (*
    rewrite (DigestRep_changeREP tp v data); trivial.
    replace_SEP  1 (data_at Tsh (tarray tuchar (Int.unsigned ctxsz)) (map Vint data) md).
    { entailer!. rewrite <- SZ3; trivial. } 
    forward_call ((Tsh,Tsh),m, md,Int.unsigned ctxsz, data).
         { rewrite Int.repr_unsigned; entailer!. }
         { simpl. cancel. }
         { simpl; split; trivial. intuition. split; trivial. apply Int.unsigned_range_2. }
    entailer!. Exists m; unfold EVP_MD_NNnode.
    rewrite ! (DigestRep_changeREP tp v data); trivial.
    entailer!. rewrite <- ! SZ3. cancel. }*)

    forward_call ((Tsh,Tsh),m, md,Int.unsigned ctxsz, Build_REPTYPE tp v). 
         { rewrite Int.repr_unsigned; entailer!. }
         { simpl. cancel. }
         { simpl; split; trivial. intuition. split; trivial. 
           split. apply Int.unsigned_range_2. rewrite SZ3; trivial. }
    entailer!. Exists m; unfold EVP_MD_NNnode; entailer!. }

  Intros m. rename H into M. forward. forward. forward. 
  forward_if (
    PROP ( )
    LOCAL (temp _t'5 (Vint (Int.repr 0)); gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at Tsh tp v md; EVP_MD_NNnode tsh vals t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, Vint Int.zero))) octx;
         data_at Tsh tp v m;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx)).
  { contradiction. }
  { clear H. forward. entailer!. }
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at Tsh tp v md; EVP_MD_NNnode tsh vals t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, Vint Int.zero))) octx;
         data_at Tsh tp v m;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx)).
  { contradiction. }
  { clear H. forward. entailer!. }
  forward. Exists Vone; unfold MDCTXHashed; entailer!.
  Exists md tp v. unfold EVP_MD_CTX_NNnode; entailer!.
  apply orp_right2. Exists m tp v; entailer!.
Time Qed.

Lemma body_EVP_MD_CTX_copy_exF: semax_body Vprog Gprog_copy_ex f_EVP_MD_CTX_copy_ex EVP_MD_CTX_copy_ex_SPEC_Finished.
Proof. 
  start_function. rename H into SZ. rename H0 into SZ1. forward.
  rewrite MDCTXInitialized_isptr'; Intros.
  rewrite MDCTXFinished_isptr'; Intros.
  rewrite EVP_MD_NNnode_isptr'; Intros.
  forward_if (
    PROP ( )
     LOCAL (temp _t'1 Vzero; temp _tmp_buf (Vint (Int.repr 0));
            gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
     SEP (ERR ep; MDCTXInitialized octx; MDCTXFinished nid ctxsz t ictx; EVP_MD_NNnode tsh vals t)).
  { clear H; 
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. apply MDCTXFinished_valid_ptr. }
  { subst; contradiction. } 
  { clear H. unfold MDCTXFinished, EVP_MD_CTX_NNnode. Intros md tp.
    unfold EVP_MD_NNnode; Intros.
    forward. forward. entailer!.
    + destruct t; try contradiction; simpl; trivial.
    + unfold MDCTXFinished, EVP_MD_NNnode, EVP_MD_CTX_NNnode. Exists md tp; entailer!. }
  forward_if (
    PROP ( )
    LOCAL (temp _tmp_buf (Vint (Int.repr 0));
           gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; MDCTXInitialized octx; MDCTXFinished nid ctxsz t ictx;
         EVP_MD_NNnode tsh vals t)).
  { elim H; trivial. }
  { clear H; forward; entailer!. }
  unfold MDCTXInitialized. forward.
  unfold MDCTXFinished, EVP_MD_CTX_NNnode; Intros md tp.
  rename H into SZ2. rename H0 into HTP. rename H1 into SZ3.
  rewrite data_at__isptr with (p:=md); Intros.
  forward.
  forward_if (
    PROP ( )
    LOCAL (temp _tmp_buf (Vint (Int.repr 0)); gvar ___stringlit_1 ep;
           temp _out octx; temp _in ictx)
    SEP (ERR ep; EVP_MD_NNnode tsh vals t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (nullval, (nullval, (nullval, nullval))) octx;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx;
         data_at_ Tsh tp md)).
  { clear H.
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer2. apply EVP_MD_NNnode_validptr. }
  { apply ptr_comp_Ceq_t in H; simpl; trivial; subst; contradiction. }
  { clear H. forward; entailer!. }
  forward_call (octx, ClInitialized).
  { simpl; unfold MDCTXInitialized; entailer!. }
  forward. simpl; unfold MDCTXInitialized. forward.
  simpl. rewrite sem_cast_neutral_ptr; simpl; trivial.
  forward.
  forward_if (
    PROP ( )
    LOCAL (temp _t'3 Vone; temp _tmp_buf (Vint (Int.repr 0));
           gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (nullval, (nullval, nullval))) octx; 
         ERR ep; data_at_ Tsh tp md; EVP_MD_NNnode tsh vals t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx)).
  { clear H. 
    apply denote_tc_test_eq_split; try apply valid_pointer_null.
    apply sepcon_valid_pointer2. apply data_at_valid_ptr; [intuition | omega ]. }
  { clear H. forward. 
    unfold EVP_MD_NNnode; Intros. rename H into TSH.
    destruct vals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
    forward. forward. entailer!. simpl. rewrite SZ2; trivial. 
    unfold EVP_MD_NNnode; entailer!. }
  { subst md; contradiction. }
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at_ Tsh tp md; EVP_MD_NNnode tsh vals t;
         EX m :_, (!!(malloc_compatible (Int.unsigned ctxsz) m) 
             && data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) octx * 
                data_at_ Tsh tp m);
         data_at Tsh (Tstruct _env_md_ctx_st noattr)
            (t, (md, (nullval, nullval))) ictx));
  [ clear H | inv H | ].
  { forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at_ Tsh tp md; EVP_MD_NNnode tsh vals t;
         EX m :_, (!!(malloc_compatible (Int.unsigned ctxsz) m) 
             && data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) octx * 
                memory_block Tsh (Int.unsigned ctxsz) m);
         data_at Tsh (Tstruct _env_md_ctx_st noattr)
            (t, (md, (nullval, nullval))) ictx));
    [ contradiction | clear H |].
    { forward. unfold EVP_MD_NNnode; Intros. rename H into TSH.
      destruct vals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
      forward.
      forward_call (Int.unsigned ctxsz). simpl; rewrite Int.repr_unsigned; apply prop_right; trivial.
      Intros m. forward. forward.
      apply semax_orp_SEPx; Intros.
      + (*m=Null*)
        subst; simpl.
        forward_if ( PROP (False) LOCAL () SEP ()).
        - clear H.
          forward_call (Vint (Int.repr 29), Vint (Int.repr 0), Vint (Int.or (Int.repr 1) (Int.repr 64)),
                 ep, Vint (Int.repr 142)).
          forward. Exists nullval. entailer!. unfold MDCTXFinished, EVP_MD_NNnode.
          Exists md tp; unfold EVP_MD_CTX_NNnode; entailer!.
          apply orp_right1. unfold MDCTXInitializedDigestSet. cancel.
        - inv H.
        - intros. unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
          old_go_lower. clear H. destruct ek; simpl; normalize. 
      + (*m<>null*)
        rename H into M. 
        rewrite memory_block_isptr; Intros.
        rewrite eval_cast_neutral_isptr; simpl; trivial.
        forward_if (
          PROP ( )
          LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
          SEP (memory_block Tsh (Int.unsigned ctxsz) m;
               data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) octx; 
               ERR ep; data_at_ Tsh tp md;
               data_at tsh (Tstruct _env_md_st noattr) (tpp, (mds, (flags, (ini, (upd, (fin, (blsize, Vint ctxsz))))))) t;
               data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx)).
        - clear H.
          apply denote_tc_test_eq_split; [ apply sepcon_valid_pointer1 | apply valid_pointer_null].
          apply sepcon_valid_pointer1. apply sepcon_valid_pointer1. apply sepcon_valid_pointer1.
          apply sepcon_valid_pointer1. apply memory_block_valid_ptr. intuition. omega.
        - destruct m; try contradiction. simpl in H. inv H.
        - clear H. forward. entailer!.
        - intros. unfold POSTCONDITION, abbreviate, overridePost; clear POSTCONDITION.
          old_go_lower. clear H. destruct ek; simpl; normalize. entailer!. 
          Exists m; unfold EVP_MD_NNnode; entailer!. }
    Intros m. rename H into M. forward. forward. forward.
    unfold EVP_MD_NNnode; Intros. rename H into TSH. 
    destruct vals as [tpp [mds [flags [ini [upd [fin [blsize ctxsize]]]]]]]; simpl in *; subst.
    forward. 
    replace_SEP 1 (data_at Tsh tp (default_val tp) md) by entailer!.
    forward_call ((Tsh,Tsh),m, md, Int.unsigned ctxsz, Build_REPTYPE tp (default_val tp)).
         { rewrite Int.repr_unsigned; entailer!. }
         { simpl. cancel. }
         { simpl; split; trivial. intuition. split; trivial.
           split. apply Int.unsigned_range_2. rewrite SZ3; trivial. }
    entailer!. Exists m; unfold EVP_MD_NNnode; entailer!. }
  Intros m. rename H into M. forward. forward. forward. 
  forward_if (
    PROP ( )
    LOCAL (temp _t'5 (Vint (Int.repr 0)); gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at_ Tsh tp md; EVP_MD_NNnode tsh vals t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, Vint Int.zero))) octx;
         data_at_ Tsh tp m;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx)).
  { contradiction. }
  { clear H. forward. entailer!. }
  forward_if (
    PROP ( )
    LOCAL (gvar ___stringlit_1 ep; temp _out octx; temp _in ictx)
    SEP (ERR ep; data_at_ Tsh tp md; EVP_MD_NNnode tsh vals t;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, Vint Int.zero))) octx;
         data_at_ Tsh tp m;
         data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (md, (nullval, nullval))) ictx)).
  { contradiction. }
  { clear H. forward. entailer!. }
  forward. Exists Vone; unfold MDCTXFinished; entailer!.
  Exists md tp. unfold EVP_MD_CTX_NNnode; entailer!.
  apply orp_right2. Exists m tp; entailer!.
Time Qed.

(*
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


Parameter preUpd :Z -> val -> mpred.
Parameter postUpd: list val -> Z -> val -> mpred.

Parameter preFin : share -> Z -> list val -> val -> mpred.


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

Definition EVP_Digest_SPEC := DECLARE _EVP_Digest
  WITH ep:val, d:val, cnt:int, md:val, sz:val, t:val, e:val,
       tsh:share, tvals:reptype (Tstruct _env_md_st noattr), ctxsz':int, mdsize:int,
       dsh:share, Data: list val, osh:share
  PRE [_data OF tptr tvoid, _count OF tuint, _out_md OF (tptr tuchar),
        _out_size OF (tptr tuint), _type OF (tptr (Tstruct _env_md_st noattr)),
        _impl OF (tptr (Tstruct _engine_st noattr)) ]
      PROP (get_ctxsize tvals = Vint ctxsz'; get_mdsize tvals = Vint mdsize;
            4 <= Int.unsigned ctxsz' <= Int.max_unsigned;
            is_pointer_or_null (get_iniptr tvals);
            readable_share dsh; readable_share tsh; writable_share osh)
      LOCAL (gvar ___stringlit_1 ep; temp _data d; temp _count (Vint cnt);
             temp _out_md md; temp _out_size sz; temp _type t; temp _impl e)
      SEP (ERR ep; EVP_MD_NNnode tsh tvals t;
           data_at dsh (tarray tuchar (Int.unsigned cnt)) Data d;
           func_ptr' ini_spec (get_iniptr tvals);
           func_ptr' upd_spec (get_updptr tvals);
           func_ptr' fin_spec (get_finptr tvals);
            if Val.eq sz nullval then emp else data_at_ Tsh tuint sz;
            memory_block osh (Int.unsigned mdsize) md)
  POST [tint] EX rv:int,
      PROP () LOCAL (temp ret_temp (Vint rv)) 
      SEP (ERR ep; EVP_MD_NNnode tsh tvals t;
           data_at dsh (tarray tuchar (Int.unsigned cnt)) Data d;
           func_ptr' ini_spec (get_iniptr tvals);
           func_ptr' upd_spec (get_updptr tvals);
           func_ptr' fin_spec (get_finptr tvals);
           (  (!!(rv=Int.zero) 
               && (memory_block osh (Int.unsigned mdsize) md *
                   if Val.eq sz nullval then emp 
                   else data_at_ Tsh tuint sz))
           || (!!(rv=Int.one)
               && (Finresult Data md *
                   if Val.eq sz nullval then emp 
                   else data_at Tsh tuint (Vint mdsize) sz)))).

Definition Gprog_EVP_Digest : funspecs :=
  (*FAILS TO TERMINATE: ltac:(with_library prog [EVP_MD_type_SPEC]). *)
  [EVP_MD_CTX_init_SPEC; EVP_DigestInit_ex_SPEC; EVP_DigestUpdate_SPEC;
   EVP_DigestFinal_ex_SPEC; EVP_MD_CTX_cleanup_SPEC4].

Axiom Ini2Upd: forall sz m, postInit sz m |-- preUpd sz m.
Axiom Upd2Fin: forall sz Data m, postUpd Data sz m |-- preFin Tsh sz Data m.

Lemma body_EVP_Digest: semax_body Vprog Gprog_EVP_Digest
                           f_EVP_Digest EVP_Digest_SPEC.
Proof. start_function. rename lvar0 into ctx.
  rename H into CTXSZ1. rename H0 into MDSZ.
  rename H1 into CTXSZ2. rename H2 into iniPN.
  rename SH into DSH. rename SH0 into TSH. rename SH1 into OSH.
  assert_PROP (field_compatible (Tstruct _env_md_ctx_st noattr) [] ctx) as FCctx by entailer!.
  rewrite (EVP_MD_NNnode_isptr'); Intros. 
  assert (CTXSZ3: Int.eq ctxsz' Int.zero = false).
  { destruct (Int.eq_dec ctxsz' Int.zero); subst.
    unfold Int.zero in CTXSZ2; rewrite Int.unsigned_repr in CTXSZ2; omega.
    rewrite Int.eq_false; trivial. }
  freeze [6;7;8] FRFin. freeze [4;6] FRUpd.
  forward_call (ctx, Tsh, sizeof (Tstruct _env_md_ctx_st noattr)).
  replace_SEP 0 (data_at Tsh (Tstruct _env_md_ctx_st noattr)
      (nullval, (nullval, (nullval, nullval))) ctx).
  { entailer!. apply convert. }
  simpl. 
  forward_call (ep, ctx, t, e, D_null Tsh nullval nullval tsh tvals ctxsz').
  { simpl. entailer!. }
  Intros ret1. simpl. focus_SEP 1.
  apply semax_orp_SEPx.
+ (* ret1 == null*)
  Intros; subst. freeze [0;1;2;3;4;5] FR3.
  forward_if (
   PROP ( )
   LOCAL (temp _t'2 (Vint Int.zero); lvar _ctx (Tstruct _env_md_ctx_st noattr) ctx;
          gvar ___stringlit_1 ep; temp _data d; 
          temp _count (Vint cnt); temp _out_md md; temp _out_size sz;
          temp _type t; temp _impl e)  SEP (FRZL FR3)).
  { elim H; trivial. }
  { clear H. forward. entailer!. }
  forward_if (
   PROP ( )
   LOCAL (temp _t'4 (Vint Int.zero); lvar _ctx (Tstruct _env_md_ctx_st noattr) ctx;
          gvar ___stringlit_1 ep; temp _data d; 
          temp _count (Vint cnt); temp _out_md md; temp _out_size sz;
          temp _type t; temp _impl e)  SEP (FRZL FR3)).
  { elim H; trivial. }
  { clear H. forward. entailer!. }
  forward. thaw FR3.
  forward_call (ctx, Tsh, nullval, nullval,
       @inr unit (share * val * reptype (Tstruct _env_md_st noattr)) (tsh,t,tvals)).
  { Exists ctxsz'; unfold EVP_MD_CTX_NNnode. entailer!.
    assert (Frame = [func_ptr' ini_spec (get_iniptr tvals); ERR ep; FRZL FRUpd; FRZL FRFin]).
    - subst Frame; reflexivity.
    - subst Frame. simpl; cancel. apply orp_right1; trivial. }
  replace_SEP 0 (data_at_ Tsh (Tstruct _env_md_ctx_st noattr) ctx).
  { entailer!. rewrite 2 data_at__memory_block. simpl; entailer!. }
  forward. Exists ctx Int.zero. entailer!.
  thaw FRUpd; thaw FRFin. cancel.
  apply orp_right1. cancel. 
+ Intros m; subst. rename H0 into M.
  thaw FRUpd; thaw FRFin. freeze [3;4] FRIni. freeze [6;7;8] FRFin.
  forward_if (
    PROP ( )
    LOCAL (temp _t'2 (Vint Int.one);
           lvar _ctx (Tstruct _env_md_ctx_st noattr) ctx;
           gvar ___stringlit_1 ep; temp _data d; 
           temp _count (Vint cnt); temp _out_md md; temp _out_size sz;
           temp _type t; temp _impl e)
    SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) ctx;
         data_at dsh (tarray tuchar (Int.unsigned cnt)) Data d;
         postUpd Data (Int.unsigned ctxsz') m; EVP_MD_NNnode tsh tvals t;
         func_ptr' upd_spec (get_updptr tvals);  FRZL FRFin; FRZL FRIni ));
    [ clear H | solve [inv H] |].
  { forward_call (ctx, Tsh, (t, (m, (nullval, nullval))), d, dsh, Data, Int.unsigned ctxsz', cnt, tsh, tvals).
    { assert (Frame = [FRZL FRFin; FRZL FRIni]).
      subst Frame; reflexivity. subst Frame; clear H; simpl; cancel.
      cancel. apply Ini2Upd. 
      (*Maybe add case to updspec for d==nullval? maybe 
        enforce ctxsz=get_ctxsize tvals again in precond of update?*) }
    forward. entailer!. }
  thaw FRFin. freeze [1;4;8] FRUpdIni.
  forward_if (
    PROP ( )
    LOCAL (temp _t'4 (Vint Int.one);
           lvar _ctx (Tstruct _env_md_ctx_st noattr) ctx;
           gvar ___stringlit_1 ep; temp _data d; 
           temp _count (Vint cnt); temp _out_md md; temp _out_size sz;
           temp _type t; temp _impl e)
    SEP (data_at Tsh (Tstruct _env_md_ctx_st noattr) (t, (m, (nullval, nullval))) ctx;
         postFin Tsh (Int.unsigned ctxsz') m;
         if Val.eq sz nullval
            then emp
            else data_at Tsh tuint (Vint mdsize) sz;
         Finresult Data md;
         EVP_MD_NNnode tsh tvals t;
         func_ptr' fin_spec (get_finptr tvals); FRZL FRUpdIni));
    [ clear H | solve [inv H] |].
  { forward_call (ctx, Tsh, (t, (m, (nullval, nullval))), md, osh, sz, tsh, tvals, ctxsz', Data, Tsh, mdsize).
    { assert (Frame = [FRZL FRUpdIni]); subst Frame; [ reflexivity | clear H; simpl; cancel].
      apply Upd2Fin. }
    { repeat split; trivial; try omega; intuition. }
    forward. entailer!. }
  forward.
  replace_SEP 1 (memory_block Tsh (Int.unsigned ctxsz') m).
  { entailer!. apply postFin_memory_block. }
  freeze [2;3;5;6] REST.
  forward_call (ctx,Tsh,m, nullval, @inr unit (share * val * reptype (Tstruct _env_md_st noattr)) (tsh,t,tvals)).
  { assert (Frame = [FRZL REST]); subst Frame; [ reflexivity | clear H; simpl].
    Exists ctxsz'; unfold EVP_MD_CTX_NNnode; entailer!.
    apply orp_right2; cancel. }
  replace_SEP 0 (data_at_ Tsh (Tstruct _env_md_ctx_st noattr) ctx).
  { entailer!. rewrite 2 data_at__memory_block. simpl; entailer!. }
  forward. Exists ctx Int.one. entailer!.
  thaw REST; thaw FRUpdIni; thaw FRIni; cancel.
  apply orp_right2. entailer!.
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
unfold Gprog, profSearchg, prog_funct; simpl.
eapply semax_func_cons.
semax_func_cons body_EVP_MD_type. apply semax_func_cons_malloc_aux.
semax_func_cons body_free.
semax_func_cons body_exit.


Definition EVP_MD_CTX_rep (p:val):mpred :=
  EX sh:_, 
  !!readable_share sh &&
  data_at sh sh (Tstruct _env_md_ctx_st noattr)
*)*) *)