Require Import Coqlib.
Require Import List.

Ltac inv N := inversion N; clear N; subst; try solve [congruence].

Definition bind {A B C: Type} (f:A -> option B) (g: B -> C) (a:A): option C :=
  match f a with None => None | Some b => Some (g b) end.
Definition bind' {A B C: Type} (f:A -> option B) (g: B -> option C) (a:A): option C :=
  match f a with None => None | Some b => (g b) end.

Definition data:Type:= Z.
Lemma data_dec: forall (d1 d2: data), { d1=d2 } + { ~  d1=d2 }. Proof. apply zeq. Qed. 
Lemma listdata_dec: forall (d1 d2: list data), { d1=d2 } + { ~  d1=d2 }. 
Proof. apply (list_eq_dec data_dec). Qed.

(*Constants defined in include/openssl/sha.h*)
Definition SHA256_DIGEST_LENGTH:Z:=32.
Definition SHA256_CBLOCK:Z :=64.
(*Constants defined in include/openssl/digest.h - not used so far
Definition EVP_MAX_MD_SIZE:Z:= 64.
Definition EVP_MAX_MD_BLOCK_SIZE:Z:= 128. *)

Section cryptoSlashdigestSlashdigestsDotc.
(*********************************  Model of crypto/digest/digests.c*********************)

(*These are the NIDs mentioned in crypto/digest/digests.c. 
Openssl_nid.h defines more but they're apparently only used elsewhere.*)
Inductive DigestNID:=
   NID_md5 
 | NID_sha1
 | NID_sha224
 | NID_sha256
 | NID_sha384
 | NID_sha512
 | NID_md5_sha1
 | NID_dsaWithSHA
 | NID_dsaWithSHA1
 | NID_ecdsa_with_SHA1
 | NID_md5WithRSAEncryption
 | NID_sha1WithRSAEncryption
 | NID_sha224WithRSAEncryption
 | NID_sha256WithRSAEncryption
 | NID_sha384WithRSAEncryption
 | NID_sha512WithRSAEncryption.

Lemma DigestNID_dec (x y :DigestNID): {x = y} + {x <> y}.
Proof. destruct x; destruct y; try solve [left; trivial]; try solve [right; intros N; congruence]. Qed.

(*These are the EVP_MD's defined in digests.c, and exported in digest.h (lines 79-89)*)
Inductive EVP_MD :=
  md4_md
| md5_md  
| sha1_md
| sha224_md
| sha256_md
| sha384_md
| sha512_md
| md5_sha1_md.
(*The concrete definitions of these digests (ie connection to EVP_MD_records) is below*)

Lemma EVP_MD_dec (m1 m2: EVP_MD): { m1=m2 } + { ~  m1=m2 }.
Proof. destruct m1; destruct m2; try solve [left; trivial]; right; discriminate. Qed.

(*TODO: complete this table in accordance with lines 240-257 of 
 crypto/digest/digests.c as more hash function are VST-verified or at 
 least modeled in Gallina*)
Definition EVP_get_digestbynid (nid:DigestNID): option EVP_MD :=
  match nid with
    NID_sha256 => Some sha256_md
 | _ => None
  end.

(*TODO (maybe): add model of EVP_get_digestbyobj*)

(********************************* End of Model of crypto/digest/digests.c*********************)
End cryptoSlashdigestSlashdigestsDotc.

Section cryptoSlashdigestSlashinternalDoth.
(******************* Model of the materal in digest/internal.h *********)
Definition mddataTp:Type:= list data.

Parameter md_ctxt_size: EVP_MD -> Z. (*TODO: fill in*)
Definition FlagsTP:=Z. (*maybe int?*)
Definition InitTP:=mddataTp.
Definition UpdateTP:=mddataTp -> list data -> mddataTp.
Definition FinalTP:=mddataTp -> list data (*result*).

(*See digest/internal.h*)
Record EVP_MD_record := 
{ EVP_MD_rec_type: DigestNID;
  EVP_MD_rec_md_size:Z;
  EVP_MD_rec_flags:FlagsTP;
  EVP_MD_rec_init: InitTP; 
  EVP_MD_rec_update: UpdateTP;
  EVP_MD_rec_final: FinalTP;
  EVP_MD_rec_block_size:Z;
  EVP_MD_rec_ctx_size:Z
}.
(**********************End of digest/internal.h model **************)
End cryptoSlashdigestSlashinternalDoth.

Section cryptoSlashdigestSlashdisgestsDotc_DigestDefinitions.
(*********************** Definitions of the various digests ***************************)

Parameter SHA256: list data -> list data. (*TODO: Import from functional_prog*)
Definition SHA256_MD: EVP_MD_record.
  econstructor.
  apply NID_sha256.
  apply SHA256_DIGEST_LENGTH.
  apply 0.
  (*Init*) { apply nil. }
  (*Update*) { red. apply app. }
  (*Final*) { red. apply SHA256. }
  apply SHA256_CBLOCK. (*Comment: why does digests.c hardcode 64 here, rather using the constant SHA256_CBLOCK?*)
  apply (md_ctxt_size sha256_md).
Defined.

End cryptoSlashdigestSlashdisgestsDotc_DigestDefinitions.

(*TODO (maybe): model the evp_md_pctx_ops record*)

(*Version in which contexts store EVP_MDs rather than EVP_MD_records:
Section cryptoSlashdigestSlashinternalDoth.
(******************* Model of the materal in digest/internal.h *********)
Definition mddataTp:Type:= list data.

Parameter md_ctxt_size: EVP_MD -> Z.

Record ENV_MD_CTX := { digest_of_ctx: EVP_MD; mddata_of_ctx: mddataTp}.

Definition FlagsTP:=Z. (*maybe int?*)
Definition InitTP:=mddataTp.
Definition UpdateTP:=mddataTp -> list data -> mddataTp.
Definition FinalTP:=mddataTp -> list data (*result*).

(*See digest/internal.h*)
Record EVP_MD_record := 
{ EVP_MD_rec_type: DigestNID;
  EVP_MD_rec_md_size:Z;
  EVP_MD_rec_flags:FlagsTP;
  EVP_MD_rec_init: InitTP; 
  EVP_MD_rec_update: UpdateTP;
  EVP_MD_rec_final: FinalTP;
  EVP_MD_rec_block_size:Z;
  EVP_MD_rec_ctx_size:Z
}.

(*TODO (maybe): model the evp_md_pctx_ops record*)
(**********************End of digest/internal.h model **************)
End cryptoSlashdigestSlashinternalDoth.

Section cryptoSlashdigestSlashdisgestsDotc_DigestDefinitions.
(*********************** Definitions of the various digests ***************************)

Parameter SHA256: list data -> list data. (*TODO: Import from functional_prog*)
Definition SHA256_MD: EVP_MD_record.
  econstructor.
  apply NID_sha256.
  apply SHA256_DIGEST_LENGTH.
  apply 0.
  (*Init*) { eapply (Build_ENV_MD_CTX sha256_md). apply nil. }
  (*Update*) { intros mddata d. eapply (Build_ENV_MD_CTX sha256_md). apply (mddata++d). }
  (*Final*) { intros mddata. apply (SHA256 mddata). }
  apply SHA256_CBLOCK. (*Comment: why does digests.c hardcode 64 here, rather using the constant SHA256_CBLOCK?*)
  apply (md_ctxt_size sha256_md).
Defined.

End cryptoSlashdigestSlashdisgestsDotc_DigestDefinitions.*)

Definition get_md_record (md:EVP_MD): option EVP_MD_record :=
  match md with
    sha256_md => Some SHA256_MD
  | _ => None
  end.

Lemma get_md_record_sound md r (R:get_md_record md = Some r):
      EVP_get_digestbynid (EVP_MD_rec_type r) = Some md.
Proof. destruct md; inv R; trivial. Qed.

(*The digest function accessors, declared in lines 180-191 of include/openssl/digest.h, 
  implemented in lines 69,73,75,77 of crypto/digest/digest.c.*)
Definition EVP_MD_type:= bind get_md_record EVP_MD_rec_type.
Definition EVP_MD_flags := bind get_md_record EVP_MD_rec_flags.
Definition EVP_MD_size := bind get_md_record EVP_MD_rec_md_size.
Definition EVP_MD_block_size := bind get_md_record EVP_MD_rec_block_size.

(*We also define accessors for the other components - these are inlined as C struct field access operations in the BoringSSL code*)
Definition EVP_MD_init:= bind get_md_record EVP_MD_rec_init.
Definition EVP_MD_updatet := bind get_md_record EVP_MD_rec_update.
Definition EVP_MD_final:= bind get_md_record EVP_MD_rec_final.
Definition EVP_MD_ctx_size:= bind get_md_record EVP_MD_rec_ctx_size.

(*The states of the abstract digest automaton*)
Inductive EVP_MD_CTX :=
  EVP_MD_CTX_emp
| EVP_MD_CTX_allocated
| EVP_MD_CTX_initialized
| EVP_MD_CTX_hashed: EVP_MD -> list data -> EVP_MD_CTX
| EVP_MD_CTX_finished.

Lemma EVP_MD_CTX_dec (e1 e2: EVP_MD_CTX): { e1 = e2 } + {~ e1 = e2}.
Proof. destruct e1; destruct e2; try solve [right; congruence]; try solve [left; auto].
destruct (EVP_MD_dec e e0); try solve [right; congruence]; subst.
destruct (listdata_dec l l0); subst; 
try solve [right; congruence]; try solve [left; auto].
Qed.

Definition EVP_MD_CTX_configured (t:EVP_MD): EVP_MD_CTX :=
  EVP_MD_CTX_hashed t nil.

Definition ctx_initialized (e:EVP_MD_CTX):Prop :=
  match e with EVP_MD_CTX_emp => False | EVP_MD_CTX_allocated => False | _ => True end.

Lemma ctx_initialized_dec: forall e, { ctx_initialized e } + { ~ ctx_initialized e }.
Proof. destruct e; simpl; try solve [left; auto]; right; auto. Qed. 

Definition ctx_allocated (e:EVP_MD_CTX):Prop :=
  match e with EVP_MD_CTX_emp => False | _ => True end.

Lemma ctx_allocated_dec: forall e, { ctx_allocated e } + { ~ ctx_allocated e }.
Proof. destruct e; simpl; try solve [left; auto]; right; auto. Qed. 

Definition ctx_configured (e:EVP_MD_CTX):option EVP_MD :=
  match e with EVP_MD_CTX_hashed md _ => Some md | _ => None end.
(*Question to Adam: should calls to DigestOperationAccessors succeed when invoked
  on a context in state EVP_MD_CTX_finished? If so, we need to tweak the above constructor  
  EVP_MD_CTX_finished to EVP_MD_CTX_finished: EVP_MD -> EVP_MD_CTX_state so that we
  have access to md in the definition of ctx_configured.*)

(*The digest operation accessors, declared in lines 225 - 242 of include/openssl/digest.h.
  Since their behavior depends on the current state of a context we model them as using
syntactic operations plus state-dependent transiations of the automaton*)
Inductive DigestOperationAccessor :=
  EVP_MD_CTX_md
| EVP_MD_CTX_size
| EVP_MD_CTX_block_size
| EVP_MD_CTX_type.

Lemma DOA_dec (x y : DigestOperationAccessor): {x = y} + {x <> y}.
Proof. destruct x; destruct y; try solve [left; trivial]; try solve [right; intros N; congruence]. Qed.

Definition DOAResultTp doa:Type :=
  match doa with
  EVP_MD_CTX_md => option EVP_MD
| EVP_MD_CTX_size => option Z
| EVP_MD_CTX_block_size => option Z
| EVP_MD_CTX_type => option DigestNID
  end.

Lemma DOAResultTp_dec {doa} (x y :DOAResultTp doa): {x = y} + {x <> y}.
Proof. destruct doa; simpl in *. 
+ destruct x; destruct y; try solve [left; trivial]; try solve [right; intros N; congruence].
  destruct (EVP_MD_dec e e0); subst; try solve [left; trivial]; try solve [right; intros N; congruence]. 
+ destruct x; destruct y; try solve [left; trivial]; try solve [right; intros N; congruence].
  destruct (zeq z z0); subst; try solve [left; trivial]; try solve [right; intros N; congruence]. 
+ destruct x; destruct y; try solve [left; trivial]; try solve [right; intros N; congruence].
  destruct (zeq z z0); subst; try solve [left; trivial]; try solve [right; intros N; congruence]. 
+ destruct x; destruct y; try solve [left; trivial]; try solve [right; intros N; congruence].
  destruct (DigestNID_dec d d0); subst; try solve [left; trivial]; try solve [right; intros N; congruence].
Qed.

Inductive doastep: forall (e1:EVP_MD_CTX) (op:DigestOperationAccessor) (r: DOAResultTp op), Prop :=
| doa_md: forall e, doastep e EVP_MD_CTX_md (ctx_configured e)
| doa_size: forall e, doastep e EVP_MD_CTX_size (bind' ctx_configured EVP_MD_size e)
| doa_blocksize: forall e, doastep e EVP_MD_CTX_block_size (bind' ctx_configured EVP_MD_block_size e)
| doa_type: forall e, doastep e EVP_MD_CTX_type (bind' ctx_configured EVP_MD_type e).

Lemma doa_md_elim: forall e e', doastep e EVP_MD_CTX_md e' -> ctx_configured e = e'.
Proof. intros. inv H. apply (Eqdep_dec.inj_pair2_eq_dec _ DOA_dec) in H2; trivial. Qed.
Lemma doa_size_elim: forall e e', doastep e EVP_MD_CTX_size e' -> bind' ctx_configured EVP_MD_size e = e'.
Proof. intros. inv H. apply (Eqdep_dec.inj_pair2_eq_dec _ DOA_dec) in H2; trivial. Qed.
Lemma doa_blocksize_elim: forall e e', doastep e EVP_MD_CTX_block_size e' -> bind' ctx_configured EVP_MD_block_size e = e'.
Proof. intros. inv H. apply (Eqdep_dec.inj_pair2_eq_dec _ DOA_dec) in H2; trivial. Qed.
Lemma doa_type_elim: forall e e', doastep e EVP_MD_CTX_type e' -> bind' ctx_configured EVP_MD_type e = e'.
Proof. intros. inv H. apply (Eqdep_dec.inj_pair2_eq_dec _ DOA_dec) in H2; trivial. Qed.

Lemma doastep_dec e x r: {doastep e x r} + {~doastep e x r}.
Proof.
destruct x.
+ destruct (DOAResultTp_dec r (ctx_configured e)); subst.
  left; econstructor.
  right; intros N. apply doa_md_elim in N. congruence.
+ destruct (DOAResultTp_dec r (bind' ctx_configured EVP_MD_size e)); subst.
  left; econstructor.
  right; intros N. apply doa_size_elim in N; congruence.
+ destruct (DOAResultTp_dec r (bind' ctx_configured EVP_MD_block_size e)); subst.
  left; econstructor.
  right; intros N. apply doa_blocksize_elim in N; congruence. 
+ destruct (DOAResultTp_dec r (bind' ctx_configured EVP_MD_type e)); subst.
  left; econstructor.
  right; intros N. apply doa_type_elim in N; congruence.
Qed. 

(*State-affecting operations*)
Inductive EvpCtxtOp:=
  MdCtxt_create
| MdCtxt_init
| MdCtxt_cleanup
| MdCtxt_destroy
| MdCtxt_copy_ex: EVP_MD_CTX -> EvpCtxtOp (*the argument here is the "in" parameter*)
| DigestInit_ex: EVP_MD -> EvpCtxtOp
| DigestInit: EVP_MD -> EvpCtxtOp
| DigestUpdate: list data -> EvpCtxtOp
| DigestFinal_ex: EvpCtxtOp
| DigestFinal: EvpCtxtOp
| DigestOpAcc: DigestOperationAccessor -> EvpCtxtOp.
(*omit | Dgst: EVP_MD -> list data -> EvpCtxtOp. one-shot "operation" -- maybe omit, 
   or treat like the accessor functions?*)

Lemma EvpCtxtOp_dec (x y : EvpCtxtOp): {x = y} + {x <> y}.
Proof. destruct x; destruct y; try solve [left; trivial]; try solve [right; intros N; congruence].
  destruct (EVP_MD_CTX_dec e e0); try solve [subst; left; trivial]; try solve [right; intros N; congruence].
  destruct (EVP_MD_dec e e0); try solve [subst; left; trivial]; try solve [right; intros N; congruence].
  destruct (EVP_MD_dec e e0); try solve [subst; left; trivial]; try solve [right; intros N; congruence].
  destruct (listdata_dec l l0); try solve [subst; left; trivial]; try solve [right; intros N; congruence].
  destruct (DOA_dec d d0); try solve [subst; left; trivial]; try solve [right; intros N; congruence].
Qed.

Definition Digest t d: list EvpCtxtOp := MdCtxt_create:: DigestInit t:: DigestUpdate d:: DigestFinal:: MdCtxt_destroy:: nil.

Inductive OpResult :=
  Success
| Fail
| Void
| MDRes: forall (t:EVP_MD) (d: list data), OpResult
| DOARes: forall doa (r: DOAResultTp doa), OpResult.

Lemma OpResult_dec (r r':OpResult): { r=r' } + {~ r=r' }.
Proof. destruct r; destruct r'; try solve [left; trivial]; try solve [right; intros N; congruence].
  destruct (EVP_MD_dec t t0); subst; try solve [left; trivial]; try solve [right; intros N; congruence].
  destruct (listdata_dec d d0); subst; try solve [left; trivial]; try solve [right; intros N; congruence].
  destruct (DOA_dec doa doa0); subst; try solve [left; trivial]; try solve [right; intros N; congruence].
  destruct (DOAResultTp_dec r r0); subst; try solve [left; trivial].
  right; intros N; inv N. apply (Eqdep_dec.inj_pair2_eq_dec _ DOA_dec) in H0; congruence.
   Qed.

Inductive step: forall (e1:EVP_MD_CTX) (op:EvpCtxtOp) (r:OpResult) (e2:EVP_MD_CTX), Prop :=
| doa_step: forall e doa r, doastep e doa r -> step e (DigestOpAcc doa) (DOARes _ r) e
| create_fail: step EVP_MD_CTX_emp MdCtxt_create Fail EVP_MD_CTX_emp
| create: step EVP_MD_CTX_emp MdCtxt_create Success EVP_MD_CTX_allocated

(*| init: step EVP_MD_CTX_allocated MdCtxt_init tt EVP_MD_CTX_initialized*)
| init: forall e, ctx_allocated e -> step e MdCtxt_init Void EVP_MD_CTX_initialized
(*maybe at this level of abstraction there's indeed no difference between init and cleanup?*)

| cleanup: forall e, e<>EVP_MD_CTX_emp -> step e MdCtxt_cleanup Success EVP_MD_CTX_initialized

| destroy: forall e, step e MdCtxt_destroy Void EVP_MD_CTX_emp

| copy_fail: forall e ctx, step e (MdCtxt_copy_ex ctx) Fail e (*spec does not say whether e is left unaltered...*)
| copy: forall e ctx, ctx_initialized e -> 
        step e (MdCtxt_copy_ex ctx) Success ctx (*note that according to digest.h, ctx can be of any 
      state, incl uninitialized (ie emp or allocated). Also, specs 
      like "returns 1 one success and 0 otherwise" are perhaps not so useful since we're not
      told what constitutes success. At this level of abstraction, we model this as nondeterminism*)
| Init_ex_fail: forall e t,
        step e (DigestInit_ex t) Fail e
| Init_ex: forall e t, ctx_initialized e -> 
        step e (DigestInit_ex t) Success (EVP_MD_CTX_configured t)

| Init: forall e t e' r, ctx_allocated e -> 
        step EVP_MD_CTX_initialized (DigestInit_ex t) r e' ->
        step e (DigestInit t) r e'

| Update: forall d t d0, 
        step (EVP_MD_CTX_hashed t d0) (DigestUpdate d) Success (EVP_MD_CTX_hashed t (d0++d))
      (*We're hardcoding list-append here...*)

| Final_ex: forall t d, 
        step (EVP_MD_CTX_hashed t d) DigestFinal_ex (MDRes t d) EVP_MD_CTX_finished
| Final: forall t d, 
        step (EVP_MD_CTX_hashed t d) DigestFinal (MDRes t d) EVP_MD_CTX_initialized.
(*omit | Digest: forall t d, 
        step EVP_MD_CTX_emp (Dgst t d) EVP_MD_CTX_emp.*)

Ltac step_determ_tac:=
  repeat match goal with [ H: step ?e ?x ?r ?e' |- _ ] => inv H end;
(*  repeat match goal with [ H: existT ?t ?op ?r = existT ?t ?op ?r' |- _] => 
    apply (Eqdep_dec.inj_pair2_eq_dec _ EvpCtxtOp_dec) in H end;*)
  subst; try solve [congruence].

Lemma step_determ x e1 e r (E:step e1 x r e) e' r' (E':step e1 x r' e') (R:r=r'): e=e'.
Proof. induction E; intros; step_determ_tac. Qed.

Lemma step_dec e1 x r e2: {step e1 x r e2} + {~step e1 x r e2}.
Proof. intros.
destruct x; destruct r;

try solve [destruct (EVP_MD_CTX_dec e1 e2); subst;
   first [solve [right; intros N; inv N; trivial] | solve [left; constructor; try congruence; try simpl; trivial] ]];

try solve [destruct e2; first [right; intros N; inv N; trivial | left; constructor; try congruence; try simpl; trivial]];

try first [
  solve [
   destruct (EVP_MD_CTX_dec e2 EVP_MD_CTX_allocated); subst;
   first [solve [right; intros N; inv N; trivial] | solve [left; constructor; try congruence; try simpl; trivial]] ]
| solve [
   destruct (EVP_MD_CTX_dec e2 EVP_MD_CTX_emp); subst;
   first [solve [right; intros N; inv N; trivial] | solve [left; constructor; try congruence; try simpl; trivial]] ]
| solve [
   destruct (EVP_MD_CTX_dec e2 EVP_MD_CTX_initialized); subst;
   first [solve [right; intros N; inv N; trivial] | solve [left; constructor; try congruence; try simpl; trivial]] ]
| solve [
   destruct (EVP_MD_CTX_dec e e2); subst;
   first [solve [right; intros N; inv N; trivial] | solve [left; constructor; try congruence; try simpl; trivial]] ]
].
+ destruct (EVP_MD_CTX_dec e1 EVP_MD_CTX_emp); subst;
    try solve [right; intros N; inv N; trivial]. 
  destruct (EVP_MD_CTX_dec e2 EVP_MD_CTX_allocated); subst;
    try solve [right; intros N; inv N; trivial]; try solve [left; constructor; try congruence; try simpl; trivial].
+ destruct (EVP_MD_CTX_dec e1 EVP_MD_CTX_emp); subst;
    try solve [right; intros N; inv N; trivial]. 
  destruct (EVP_MD_CTX_dec e2 EVP_MD_CTX_emp); subst;
    try solve [right; intros N; inv N; trivial]; try solve [left; constructor; try congruence; try simpl; trivial].
+ destruct (ctx_allocated_dec e1); subst;
    try solve [right; intros N; inv N; trivial]. 
  destruct (EVP_MD_CTX_dec e2 EVP_MD_CTX_initialized); subst;
    try solve [right; intros N; inv N; trivial]; try solve [left; constructor; try congruence; try simpl; trivial].
+ destruct (EVP_MD_CTX_dec e1 EVP_MD_CTX_emp); subst;
    try solve [right; intros N; inv N; trivial]. 
  destruct (EVP_MD_CTX_dec e2 EVP_MD_CTX_initialized); subst;
    try solve [right; intros N; inv N; trivial]; try solve [left; constructor; try congruence; try simpl; trivial].
+ destruct (ctx_initialized_dec e1); subst;
    try solve [right; intros N; inv N; trivial]. 
  destruct (EVP_MD_CTX_dec e e2); subst;
    try solve [right; intros N; inv N; trivial]; try solve [left; constructor; try congruence; try simpl; trivial].
+ destruct (ctx_initialized_dec e1); subst;
    try solve [right; intros N; inv N; trivial]. 
  destruct (EVP_MD_CTX_dec e2 (EVP_MD_CTX_configured e)); subst;
    try solve [right; intros N; inv N; trivial]; try solve [left; constructor; try congruence; try simpl; trivial].
+ destruct (ctx_allocated_dec e1); try solve [right; intros N; inv N].
  destruct (EVP_MD_CTX_dec e2 (EVP_MD_CTX_configured e)); subst.
  - left. constructor. trivial. econstructor; simpl; trivial. 
  - right; intros N; inv N. inv H2.
+ destruct (ctx_allocated_dec e1); try solve [right; intros N; inv N].
  assert (step EVP_MD_CTX_initialized (DigestInit_ex e) Fail EVP_MD_CTX_initialized).
  - constructor.
  - destruct (EVP_MD_CTX_dec e2 EVP_MD_CTX_initialized); subst.
    * left. constructor; trivial.
    * right; intros N; inv N. inv H3.
+ right; intros N; inv N. inv H2. 
+ right; intros N; inv N. inv H2.
+ right; intros N; inv N. inv H2. 
+ destruct e1; try solve [ right; intros N; inv N].
  destruct (EVP_MD_CTX_dec e2 (EVP_MD_CTX_hashed e (l0++l))); subst; try solve [ right; intros N; inv N].
  left; constructor.
+ destruct e1; try solve [ right; intros N; inv N].
  destruct (EVP_MD_CTX_dec e2 EVP_MD_CTX_finished); subst; try solve [ right; intros N; inv N].
  destruct (EVP_MD_dec t e); subst; try solve [ right; intros N; inv N].
  destruct (listdata_dec l d); subst; try solve [ right; intros N; inv N].
  left; constructor.
+ destruct e1; try solve [ right; intros N; inv N].
  destruct (EVP_MD_CTX_dec e2 EVP_MD_CTX_initialized); subst; try solve [ right; intros N; inv N].
  destruct (EVP_MD_dec t e); subst; try solve [ right; intros N; inv N].
  destruct (listdata_dec l d); subst; try solve [ right; intros N; inv N].
  left; constructor.
+ destruct (DOA_dec d doa); subst; try solve [ right; intros N; inv N].
  destruct (doastep_dec e1 doa r); subst.
  - destruct (EVP_MD_CTX_dec e1 e2); subst. left; econstructor; trivial.
    right; intros N; inv N.
  - right; intros N; inv N. apply (Eqdep_dec.inj_pair2_eq_dec _ DOA_dec) in H1; congruence.
Qed.

(*Results of single steps are hidden, as long as the sequence of states fits together*)
Inductive step_star: EVP_MD_CTX -> list EvpCtxtOp -> list OpResult -> EVP_MD_CTX -> Prop :=
  step_zero: forall e, step_star e nil nil e
| step_one: forall e1 x e2 l r rs e3, step e1 x r e2 -> step_star e2 l rs e3 -> step_star e1 (x::l) (r::rs) e3.

Ltac step_star_dec_aux:= try solve [right; intros N; inv N;
     match goal with [ H: step ?e1 ?op ?r ?e2 |- _ ] => inv H end].

Lemma step_star_dec: forall l rs e1 e2, {step_star e1 l rs e2} + {~step_star e1 l rs e2}.
Proof.
  induction l; simpl; intros.
+ destruct (EVP_MD_CTX_dec e1 e2); subst; step_star_dec_aux. 
  destruct rs; subst; step_star_dec_aux.  
  left; constructor.
+ destruct rs; step_star_dec_aux.  
  destruct a.
  - (*MdCtxt_create*)
    destruct (EVP_MD_CTX_dec e1 EVP_MD_CTX_emp); subst; step_star_dec_aux.  
    destruct (OpResult_dec o Fail); subst.
    * destruct (IHl rs EVP_MD_CTX_emp e2); step_star_dec_aux. 
      left. econstructor. apply create_fail; trivial. trivial.
    * destruct (OpResult_dec o Success); subst; step_star_dec_aux. 
      destruct (IHl rs EVP_MD_CTX_allocated e2);step_star_dec_aux. 
      left. econstructor. apply create; trivial. trivial.
  - (*MdCtxt_init*)
    destruct (ctx_allocated_dec e1); step_star_dec_aux.
    destruct (OpResult_dec o Void); subst; step_star_dec_aux. 
    destruct (IHl rs EVP_MD_CTX_initialized e2); step_star_dec_aux.
    left. econstructor. apply init; trivial. trivial.
  - (*MdCtxt_cleanup*)
    destruct (EVP_MD_CTX_dec e1 EVP_MD_CTX_emp); subst; step_star_dec_aux.  
    destruct (IHl rs EVP_MD_CTX_initialized e2); step_star_dec_aux.  
    destruct (OpResult_dec o Success); subst; step_star_dec_aux.  
    left. econstructor. apply cleanup; trivial. trivial.
  - (*MdCtxt_destroy*)
    destruct (IHl rs EVP_MD_CTX_emp e2); step_star_dec_aux.  
    destruct (OpResult_dec o Void); subst; step_star_dec_aux.  
    left. econstructor. apply destroy; trivial. trivial.
  - (*MdCtxt_copy_ex*)
    destruct (OpResult_dec o Fail); subst. 
    * destruct (IHl rs e1 e2); step_star_dec_aux. 
      left. econstructor. apply copy_fail; trivial. trivial.
    * destruct (OpResult_dec o Success); subst; step_star_dec_aux. 
      destruct (ctx_initialized_dec e1); step_star_dec_aux. 
      destruct (IHl rs e e2); step_star_dec_aux.
      left. econstructor. apply copy; trivial. trivial.
  - (*DigestInit_ex*)
    destruct (OpResult_dec o Fail); subst. 
    * destruct (IHl rs e1 e2); step_star_dec_aux. 
      left. econstructor. apply Init_ex_fail; trivial. trivial.
    * destruct (ctx_initialized_dec e1); step_star_dec_aux.
      destruct (IHl rs (EVP_MD_CTX_configured e) e2); step_star_dec_aux.
      destruct (OpResult_dec o Success); subst; step_star_dec_aux.  
      left. econstructor. apply Init_ex; trivial. trivial.
  - (*DigestInit*)
    destruct (ctx_allocated_dec e1); step_star_dec_aux.  
    destruct (OpResult_dec o Fail); subst.
    * destruct (IHl rs EVP_MD_CTX_initialized e2).
      ++ left. econstructor. apply Init. trivial. constructor. trivial.
      ++ right; intros N; inv N. inv H5. inv H2. 
    * destruct (OpResult_dec o Success); subst. 
      ++ destruct (IHl rs (EVP_MD_CTX_configured e) e2).
         -- left. econstructor. apply Init. trivial. constructor. simpl; trivial. trivial.
         -- right; intros N; inv N. inv H5. inv H2.
      ++ right; intros N; inv N. inv H5. inv H2.
  - (*DigestUpdate*)
    destruct e1; step_star_dec_aux. 
    destruct (OpResult_dec o Success); subst; step_star_dec_aux. 
    destruct (IHl rs (EVP_MD_CTX_hashed e (l1++l0)) e2); step_star_dec_aux.
    left; econstructor. constructor. trivial.
  - (*DigestFinal_ex*)
    destruct e1;  step_star_dec_aux.
    destruct (OpResult_dec o (MDRes e l0)); subst; step_star_dec_aux. 
    destruct (IHl rs EVP_MD_CTX_finished e2); step_star_dec_aux.
    left; econstructor. constructor. trivial.
  - (*DigestFinal*)
    destruct e1; step_star_dec_aux.
    destruct (OpResult_dec o (MDRes e l0)); subst; step_star_dec_aux.
    destruct (IHl rs EVP_MD_CTX_initialized e2); step_star_dec_aux.
    left; econstructor. constructor. trivial.
  - (*DOA*)
    destruct o; step_star_dec_aux.
    destruct (DOA_dec doa d); subst; step_star_dec_aux. 
    destruct (doastep_dec e1 d r).
    * destruct (IHl rs e1 e2); step_star_dec_aux.
      left. econstructor. constructor. trivial. trivial.
    * right; intros N; inv N. inv H5. apply (Eqdep_dec.inj_pair2_eq_dec _ DOA_dec) in H1; congruence.
Qed.

Lemma Digest_step_star t d e r: step_star EVP_MD_CTX_emp (Digest t d) r e <-> 
      e = EVP_MD_CTX_emp /\ r = Success :: Success :: Success :: MDRes t d :: Void :: nil.
Proof. unfold Digest.
split; intros.
+ inv H. inv H3; inv H6.
  - inv H2; contradiction.
  - inv H2; simpl in *. clear H0; inv H3; inv H5.
    * inv H2.
    * inv H3. inv H7. inv H3. inv H6. inv H3. inv H7. split; trivial.
+ destruct H; subst. repeat econstructor.
Qed. 

Lemma NoFinalsORUpdatesAfterFinals e2 l e1 i j r
 (I: i=DigestFinal_ex \/ i=DigestFinal)
 (J: j=DigestFinal_ex \/ j=DigestFinal \/ exists d, j=DigestUpdate d):
 ~ step_star e1 (i::j::l) r e2.
Proof. 
  intros N.
  destruct I; subst.
* inv N. inv H2. inv H5. 
  destruct J as [J | [J | [dd J]]]; subst; inv H2. 
* inv N. inv H2. inv H5. 
  destruct J as [J | [J | [dd J]]]; subst; inv H2. 
Qed.

Lemma AfterFinals_trace e2 l e1 i r
 (I: i=DigestFinal_ex \/ i=DigestFinal)
 (STEPS: step_star e1 (i::l) r e2):
 exists t d tl, r= MDRes t d :: tl.
Proof.
  inv STEPS.
  destruct I; subst; inv H2; eexists; eexists; eexists; reflexivity.
Qed. 