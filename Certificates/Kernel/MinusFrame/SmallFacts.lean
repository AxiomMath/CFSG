module

public import Certificates.Kernel.MinusFrame.SmallChecks
public import Certificates.Kernel.MinusFrame.Glue
public import CFSG.Certificates.Kernel.BfsPinAlg
public import CFSG.Certificates.Kernel.BfsPinBaseSound
public import CFSG.Certificates.Kernel.Misc.PermWitSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CertificateChecks.KernelMinusFrame

open CFSG.OddTranspositions.PartThree CFSG.OddTranspositions.PartThree.MinusFrame
open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.PermWit CFSG.KC.PermPinK
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
local notation "AI" => CFSG.KS.Raw.Orb.allN_iff

theorem and_of {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by
  simpa using h

theorem keysOK : ∀ p ∈ minusBase, p < 65 := by decide

theorem numsS : S0.ng = 3 ∧ S0.N = 16 ∧ SL.ng = 15 ∧ SL.N = 120 ∧ SA.ng = 2 ∧ SA.N = 60 := by
  have h := kNumsS
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  tauto

theorem bind0 : t0Gens.size = 3 ∧ ∀ k < 3, t0Gens[k]! = unpack 65 7 (S0.G k) :=
  binds_of_check kBind0

theorem bindL : l0Gens.size = 15 ∧ ∀ k < 15, l0Gens[k]! = unpack 65 7 (SL.G k) :=
  binds_of_check kBindL

theorem bindA : aGens.size = 2 ∧ ∀ k < 2, aGens[k]! = unpack 65 7 (SA.G k) :=
  binds_of_check kBindA

theorem perm0 : ∀ k < S0.ng,
    permOK 65 7 (mask 7) (65 * 7) (S0.G k) (pinvS 65 7 (mask 7) (S0.G k)) = true := by
  intro k hk
  rw [numsS.1] at hk
  exact AI.1 (and_of (and_of kPermS).1).1 k hk

theorem permL : ∀ k < SL.ng,
    permOK 65 7 (mask 7) (65 * 7) (SL.G k) (pinvS 65 7 (mask 7) (SL.G k)) = true := by
  intro k hk
  rw [numsS.2.2.1] at hk
  exact AI.1 (and_of (and_of kPermS).1).2 k hk

theorem permA : ∀ k < SA.ng,
    permOK 65 7 (mask 7) (65 * 7) (SA.G k) (pinvS 65 7 (mask 7) (SA.G k)) = true := by
  intro k hk
  rw [numsS.2.2.2.2.1] at hk
  exact AI.1 (and_of kPermS).2 k hk

theorem pin0 : (t0Cert ()).pts = Array.ofFn (n := S0.N) fun i => unpack 65 7 (S0.T i.val) :=
  enumBfs_pts_base (by rw [bind0.1, numsS.1])
    (fun k hk => bind0.2 k (by rw [numsS.1] at hk; exact hk)) S0.ok keysOK kK0
    (by have := numsS.2.1; omega)

theorem pinL : (l0Cert ()).pts = Array.ofFn (n := SL.N) fun i => unpack 65 7 (SL.T i.val) :=
  enumBfs_pts_base (by rw [bindL.1, numsS.2.2.1])
    (fun k hk => bindL.2 k (by rw [numsS.2.2.1] at hk; exact hk)) SL.ok keysOK kKL
    (by have := numsS.2.2.2.1; omega)

theorem pinA : (aCert ()).pts = Array.ofFn (n := SA.N) fun i => unpack 65 7 (SA.T i.val) :=
  enumBfs_pts_base (by rw [bindA.1, numsS.2.2.2.2.1])
    (fun k hk => bindA.2 k (by rw [numsS.2.2.2.2.1] at hk; exact hk)) SA.ok keysOK kKA
    (by have := numsS.2.2.2.2.2; omega)

theorem enum0 : enumOK 65 t0Gens minusBase (t0Cert ()) = true :=
  enumOK_of_bfsK_base (by rw [bind0.1, numsS.1])
    (fun k hk => bind0.2 k (by rw [numsS.1] at hk; exact hk)) perm0 S0.ok keysOK kK0
    (by have := numsS.2.1; omega)

theorem enumL : enumOK 65 l0Gens minusBase (l0Cert ()) = true :=
  enumOK_of_bfsK_base (by rw [bindL.1, numsS.2.2.1])
    (fun k hk => bindL.2 k (by rw [numsS.2.2.1] at hk; exact hk)) permL SL.ok keysOK kKL
    (by have := numsS.2.2.2.1; omega)

theorem enumA : enumOK 65 aGens minusBase (aCert ()) = true :=
  enumOK_of_bfsK_base (by rw [bindA.1, numsS.2.2.2.2.1])
    (fun k hk => bindA.2 k (by rw [numsS.2.2.2.2.1] at hk; exact hk)) permA SA.ok keysOK kKA
    (by have := numsS.2.2.2.2.2; omega)

theorem memK_eq {N : Nat} {T : Nat → Nat} {x : Nat} :
    memK N T x = (List.range N).any (fun j => Nat.beq x (T j)) := by
  apply Bool.eq_iff_iff.2
  rw [List.any_eq_true]
  constructor
  · intro h
    obtain ⟨j, hj, e⟩ := memK_spec h
    exact ⟨j, List.mem_range.2 hj, by rw [e, Nat.beq_refl]⟩
  · rintro ⟨j, hj, e⟩
    unfold memK
    cases h : allN N (fun j => Bool.rec (motive := fun _ => Bool) true false (Nat.beq x (T j)))
    · rfl
    · have h1 := allN_spec h j (List.mem_range.1 hj)
      rw [e] at h1
      exact absurd h1 Bool.false_ne_true

theorem any_pin {c : ArrCert} {N : ℕ} {T : ℕ → ℕ}
    (hc : c.pts = Array.ofFn (n := N) fun i => unpack 65 7 (T i.val))
    (hT : ∀ i < N, canonK 65 7 (mask 7) (65 * 7) (T i) = true) {p : ℕ}
    (hp : canonK 65 7 (mask 7) (65 * 7) p = true) :
    c.pts.toList.any (eqA 65 (unpack 65 7 p)) = memK N T p := by
  rw [hc, pts_toList (fun i => unpack 65 7 (T i)), List.any_map, memK_eq]
  apply Bool.eq_iff_iff.2
  simp only [List.any_eq_true, List.mem_range, Function.comp]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, by rwa [eqA_unpack hp (hT j hj)] at h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, hj, by rwa [eqA_unpack hp (hT j hj)]⟩

theorem keyInj {N : ℕ} {T : ℕ → ℕ} {SK : List ℕ} (hK : keysSK 65 7 minusBase N T SK = true) :
    ∀ i < N, ∀ j < N, keyA 65 minusBase (unpack 65 7 (T i)) =
      keyA 65 minusBase (unpack 65 7 (T j)) → i = j := by
  intro i hi j hj e
  rw [keyA_unpack keysOK, keyA_unpack keysOK] at e
  exact keysSK_spec hK i hi j hj e

theorem t0Chk : t0Check (t0Cert ()) = true := by
  have h : (t0Cert ()).pts.size = 16 := by rw [pin0, Array.size_ofFn, numsS.2.1]
  simp [t0Check, enum0, h]

theorem frameMem : frameMemCheck (t0Cert ()) = true := by
  unfold frameMemCheck
  rw [List.all_eq_true]
  intro k hk
  have hk' := List.mem_range.1 hk
  have hk2 : k < CertificateChecks.KernelMinusEnum.ME.ng := by
    rw [CertificateChecks.KernelMinusEnum.nums.1]; exact hk'
  rw [CertificateChecks.KernelMinusEnum.bind.2 k hk2,
    any_pin pin0 (bfsK_canon S0.ok) (allN_spec CertificateChecks.KernelMinusEnum.kG k hk2)]
  exact allN_spec kFrameMem k hk'

theorem cent_lt' (i : Fin 15) : centArr[(i : ℕ)]! < 65 := by
  revert i
  decide

theorem l0Chk : l0Check () = true := by
  unfold l0Check
  dsimp only
  rw [enumL, pinL, Array.size_ofFn, numsS.2.2.2.1, pts_toList (fun i => unpack 65 7 (SL.T i))]
  simp only [Bool.true_and, beq_self_eq_true, List.all_eq_true, List.any_map, List.any_eq_true,
    Function.comp, List.mem_range]
  intro a _ b _
  have h := AI.1 (AI.1 kTrans a a.2) b b.2
  by_contra hne
  have hall : allN 120 (fun j => !(Nat.beq (pg 7 (mask 7) (SL.T j) centArr[(a : ℕ)]!)
      centArr[(b : ℕ)]!)) = true := by
    refine allN_intro fun j hj => ?_
    cases e : Nat.beq (pg 7 (mask 7) (SL.T j) centArr[(a : ℕ)]!) centArr[(b : ℕ)]!
    · rfl
    · refine absurd ⟨j, hj, ?_⟩ hne
      rw [unpack_get' (cent_lt' a), beq_iff_eq]
      exact Nat.eq_of_beq_eq_true e
  rw [hall] at h
  exact Bool.false_ne_true h

theorem simpleA : conjSimpleOK 65 minusBase (aCert ()) = true := by
  have hN := numsS.2.2.2.2.2
  refine conjSimpleOK_of_ctree (WT := WA) CertificateChecks.KernelMinusEnum.kSz keysOK enumA pinA
    (fun i hi => AI.1 kPermTA i (by rw [hN] at hi; exact hi))
    (Nat.eq_of_beq_eq_true kT0A) (keyInj kKA) (fun k hk => ?_)
  rw [hN] at hk ⊢
  have h := AI.1 kTreeA k hk
  rw [Bool.or_eq_true] at h
  exact h.imp id fun h' => AI.1 h'

theorem aNotT : (aCert ()).pts.toList.all (fun g => !(eqA 65 g (tArr ()))) = true := by
  rw [pinA, pts_toList (fun i => unpack 65 7 (SA.T i)), List.all_map, List.all_eq_true, bindX.1]
  intro j hj
  rw [List.mem_range] at hj
  simp only [Function.comp]
  rw [eqA_unpack (bfsK_canon SA.ok j hj) (canonX (by omega))]
  exact AI.1 (and_of kA).1 j (by rw [numsS.2.2.2.2.2] at hj; exact hj)

theorem aSub : (aGens.toList.all fun a => (l0Cert ()).pts.toList.any (eqA 65 a)) = true := by
  rw [List.all_eq_true]
  intro a ha
  obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem (Array.mem_def.2 ha)
  have hk' : k < 2 := by
    have := bindA.1
    omega
  have hk2 : k < SA.ng := by rw [numsS.2.2.2.2.1]; exact hk'
  suffices h : (l0Cert ()).pts.toList.any (eqA 65 aGens[k]!) = true by
    rwa [getElem!_pos aGens k hk] at h
  rw [bindA.2 k hk', any_pin pinL (bfsK_canon SL.ok) (PP_gen SA.ok permA k hk2).1]
  have h := AI.1 (and_of kA).2 k hk'
  rwa [numsS.2.2.2.1]

theorem aChk : aCheck () = true := by
  unfold aCheck
  dsimp only
  have hsz : (aCert ()).pts.size = 60 := by rw [pinA, Array.size_ofFn, numsS.2.2.2.2.2]
  rw [enumA, hsz, aNotT, aSub, simpleA]
  rfl

end CertificateChecks.KernelMinusFrame

end
