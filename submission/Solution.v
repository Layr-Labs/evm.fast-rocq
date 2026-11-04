From Galette Require Import Base.
From Galette.HOL.src.n_bit Require Import words.
From InitE.InitE Require Import NatE SubmissionModel Challenge.
From InitE.Baseline Require Import Artifacts Submission BitmapImageFacts BaselineCertificate.
From SubmissionLiterals Require Import Values.
Open Scope N_scope.
Definition submission : Submission := baselineSubmission.
Lemma submitted_code_binding : submittedCode = Artifacts.code.
Proof. apply word_list_numeric_ext; vm_compute; reflexivity. Qed.
Definition certificate : Certificate
 (Build_Submission submittedCode claimedScore (anchorPc submission)
  (names submission) (first submission) (extra submission)) claimedScore.
Proof. rewrite submitted_code_binding; exact baseline_certificate. Qed.

(* Solver first-entry marker (blocksek, Muse Spark).

   Provenance and sanity facts for the initial infinity submission on
   [eigenlabs/evm-fast-rocq/rocq]. The certificate above is the organizer
   baseline ([baselineSubmission] with an infinity claim); the lemmas below
   are solver-authored checks that the submission assembles as claimed.
   All proofs are [reflexivity]/[exact I] over fixed definitions; they add
   no axioms and change no ROM bytes, scores, or certificate statements. *)

(** The solver submission reference agrees with the baseline by definition. *)
Lemma solver_submission_is_baseline : submission = baselineSubmission.
Proof. reflexivity. Qed.

(** Marker that this solver addition elaborated with the submission. *)
Lemma solver_module_present : True.
Proof. exact I. Qed.
