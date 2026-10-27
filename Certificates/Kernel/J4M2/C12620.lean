module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4L0StructData
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4L0StructData
public import Certificates.Kernel.J4M2.C12633
import CFSG.Certificates.Kernel.Common.Harness
public meta import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentCEData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentCEData
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public meta import CFSG.Open.Defs
public import CFSG.Open.Defs
public import CFSG.Sporadic.Th.F2Spec
public meta import CFSG.Sporadic.Th.F2Spec

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ4M2

open CFSG.KC.J4Q CFSG.KD.J4Q CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT2A
  CFSG.Quasithin.J4M2 CertificateChecks.KernelJ4Q CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

@[expose] noncomputable def wgK (w : List Nat) : Nat := w.foldl (fun acc n => mulJ c rm acc (gmK n)) one

@[expose] noncomputable def hitK (i : Nat) : Nat := wgK (lsHitWords.getD i [])

@[expose] noncomputable def hprodK (idx : List Nat) : Nat := idx.foldl (fun acc i => mulJ c rm acc (hitK i)) one

theorem words_lt : ∀ i < 6, ∀ n ∈ lsHitWords.getD i [], n < 32 := by decide

theorem wg_enc (w : List Nat) (hw : ∀ n ∈ w, n < 32) :
    WfA (w.foldl (fun acc n => mulRows acc gmats[n]!) (idRows ())) ∧
      encR (w.foldl (fun acc n => mulRows acc gmats[n]!) (idRows ())) = wgK w := by
  have key : ∀ (l : List Nat), (∀ n ∈ l, n < 32) → ∀ (acc : Array V2) (a : Nat),
      WfA acc ∧ encR acc = a → WfA (l.foldl (fun acc n => mulRows acc gmats[n]!) acc) ∧
        encR (l.foldl (fun acc n => mulRows acc gmats[n]!) acc) =
          l.foldl (fun acc n => mulJ c rm acc (gmK n)) a := by
    intro l
    induction l with
    | nil => intro _ acc a h; exact h
    | cons n l ih =>
      intro hl acc a h
      rw [List.foldl_cons, List.foldl_cons]
      exact ih (fun i hi => hl i (List.mem_cons_of_mem _ hi)) _ _
        (mul_enc hK h (gm_enc (hl n List.mem_cons_self)))
  exact key w hw _ _ (id_enc hK)

theorem hit_enc {i : Nat} (hi : i < 6) : WfA (lsHitRows i) ∧ encR (lsHitRows i) = hitK i :=
  wg_enc _ (words_lt i hi)

theorem hprod_enc (idx : List Nat) (hidx : ∀ i ∈ idx, i < 6) :
    WfA (lsProdRows idx) ∧ encR (lsProdRows idx) = hprodK idx := by
  have key : ∀ (l : List Nat), (∀ i ∈ l, i < 6) → ∀ (acc : Array V2) (a : Nat),
      WfA acc ∧ encR acc = a → WfA (l.foldl (fun acc i => mulRows acc (lsHitRows i)) acc) ∧
        encR (l.foldl (fun acc i => mulRows acc (lsHitRows i)) acc) =
          l.foldl (fun acc i => mulJ c rm acc (hitK i)) a := by
    intro l
    induction l with
    | nil => intro _ acc a h; exact h
    | cons n l ih =>
      intro hl acc a h
      rw [List.foldl_cons, List.foldl_cons]
      exact ih (fun i hi => hl i (List.mem_cons_of_mem _ hi)) _ _
        (mul_enc hK h (hit_enc (hl n List.mem_cons_self)))
  exact key idx hidx _ _ (id_enc hK)

theorem ls_chk : ((List.range 6).all (fun i => Nat.beq (mulJ c rm (hitK i) cK) (mulJ c rm cK (hitK i))) &&
    Nat.beq (powJ c rm one YB 3) one &&
    Nat.beq (powJ c rm one (powJ c rm one (hprodK lsAIdx) lsAExp) 7) one &&
    Nat.beq (powJ c rm one (powJ c rm one (hprodK lsBIdx) lsBExp) 7) one &&
    Nat.beq (powJ c rm one (mulJ c rm (powJ c rm one (hprodK lsAIdx) lsAExp)
      (powJ c rm one (hprodK lsBIdx) lsBExp)) 7) cK) = true := by quickRfl

theorem ls_ok : lsOK () = true := by
  have h := ls_chk
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have hA : WfA (lsARows ()) ∧ encR (lsARows ()) = powJ c rm one (hprodK lsAIdx) lsAExp :=
    pow_enc hK (hprod_enc _ (by decide)) _
  have hB : WfA (lsBRows ()) ∧ encR (lsBRows ()) = powJ c rm one (hprodK lsBIdx) lsBExp :=
    pow_enc hK (hprod_enc _ (by decide)) _
  have hb : WfA gmats[13]! ∧ encR gmats[13]! = YB := gm_enc (n := 13) (by omega)
  unfold lsOK
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, by decide⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro i hi
    have hi' := List.mem_range.1 hi
    have hh := hit_enc hi'
    unfold lsHitAt
    have hw : wfR (lsHitRows i) = true := wf_bool hh.1
    rw [hw, Bool.true_and, eqRows_of (mul_enc hK hh cMat_encK) (mul_enc hK cMat_encK hh)]
    exact List.all_eq_true.1 h1 i hi
  · rw [eqRows_of (pow_enc hK hb 3) (id_enc hK)]
    exact h2
  · rw [eqRows_of (pow_enc hK hA 7) (id_enc hK)]
    exact h3
  · rw [eqRows_of (pow_enc hK hB 7) (id_enc hK)]
    exact h4
  · rw [eqRows_of (pow_enc hK (mul_enc hK hA hB) 7) cMat_encK]
    exact h5

open CFSG.AGLEmbeddingD2.Wilson.NormalizerAction in
theorem c12620 : lsOK () = true := ls_ok

end CertificateChecks.KernelJ4M2

end
