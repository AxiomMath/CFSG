module

public import Certificates.Kernel.LocalComp.L34Cos.Chk
public import Certificates.Kernel.LocalComp.L34Cert
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4L34CertInputs
import Certificates.Kernel.Sporadic.ON.Gen
import CFSG.Certificates.Kernel.L34KSnd.Tab
import CFSG.Certificates.Kernel.L34ScanSound
import CFSG.Certificates.Kernel.Spor.PEnumSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

#kon_join CertificateChecks.KernelLC.L34Cos.orbCAll CertificateChecks.KernelLC.L34Cos.orbC 8
#kon_join CertificateChecks.KernelLC.L34Cos.notRowAll CertificateChecks.KernelLC.L34Cos.notRow 8

namespace CertificateChecks.KernelLC.L34Cos

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.KC.L34Scan
open CertificateChecks.KernelLC CertificateChecks.KernelLC.L34X CertificateChecks.KernelLC.L34Cert
open CFSG.PSL3Four.Native CFSG.ComponentClassification.CatFactsL4U4

theorem cn {p q : Nat} (hp : canonK 42 6 (mask 6) (42 * 6) p = true)
    (hq : canonK 42 6 (mask 6) (42 * 6) q = true) :
    canonK 42 6 (mask 6) (42 * 6) (pcomp 42 6 (mask 6) p q) = true :=
  CFSG.KC.BfsPin.canonK_pcomp hp hq

theorem allN' {n : Nat} {f : Nat → Bool} (h : allN n f = true) : ∀ i < n, f i = true :=
  CFSG.KS.Raw.Orb.allN_iff.1 h

theorem cGI3 : canonK 42 6 (mask 6) (42 * 6) (GI 3) = true :=
  (andB_iff.1 (allN' kGI2005 3 (by decide))).1

theorem eGI3 : pcomp 42 6 (mask 6) (L34R.G 3) (GI 3) = pidn 42 6 :=
  Nat.eq_of_beq_eq_true (andB_iff.1 (allN' kGI2005 3 (by decide))).2

theorem e4 : g₄T = unpack 42 6 (L34R.G 3) := g_eq (k := 3) (by decide)

theorem eg4i : g4iT = unpack 42 6 (GI 3) := by
  unfold g4iT
  rw [e4]
  exact invTab_eq_of_pcomp (cnG (by decide)) cGI3 eGI3

theorem conj4_eq (x : Nat) (hx : canonK 42 6 (mask 6) (42 * 6) x = true) :
    conjTab 42 g₄T g4iT (unpack 42 6 x) = unpack 42 6 (cj4 x) := by
  unfold conjTab cj4
  rw [e4, eg4i, comp_unpack' (cnG (by decide)) hx, comp_unpack' (cn (cnG (by decide)) hx) cGI3]

theorem conj44_eq (x : Nat) (hx : canonK 42 6 (mask 6) (42 * 6) x = true) :
    conjTab 42 g44T g44iT (unpack 42 6 x) = unpack 42 6 (cj44 x) := by
  have c3 : canonK 42 6 (mask 6) (42 * 6) (L34R.G 3) = true := cnG (by decide)
  unfold conjTab cj44 g44T g44iT
  rw [e4, eg4i, comp_unpack' c3 c3, comp_unpack' cGI3 cGI3, comp_unpack' (cn c3 c3) hx,
    comp_unpack' (cn (cn c3 c3) hx) (cn cGI3 cGI3)]

theorem hrepK : ∀ s < 8, repT[s]! = unpack 42 6 (repK s) := by
  intro s hs
  match s, hs with
  | 0, _ => exact r1_eq
  | 1, _ => exact e5
  | 2, _ =>
    have e : repT[2]! = conjTab 42 g₄T g4iT g₅T := rfl
    have e' : repK 2 = cj4 (L34R.G 4) := rfl
    rw [e, e', e5]
    exact conj4_eq _ (cnG (by decide))
  | 3, _ =>
    have e : repT[3]! = conjTab 42 g44T g44iT g₅T := rfl
    have e' : repK 3 = cj44 (L34R.G 4) := rfl
    rw [e, e', e5]
    exact conj44_eq _ (cnG (by decide))
  | 4, _ => exact e6
  | 5, _ =>
    have e : repT[5]! = conjTab 42 g₄T g4iT g₆T := rfl
    have e' : repK 5 = cj4 (L34R.G 5) := rfl
    rw [e, e', e6]
    exact conj4_eq _ (cnG (by decide))
  | 6, _ =>
    have e : repT[6]! = conjTab 42 g44T g44iT g₆T := rfl
    have e' : repK 6 = cj44 (L34R.G 5) := rfl
    rw [e, e', e6]
    exact conj44_eq _ (cnG (by decide))
  | 7, _ => exact r4_eq

theorem hrep {s : Nat} (hs : s < 8) : repT[s]! = unpack 42 6 (RQ s) ∧
    canonK 42 6 (mask 6) (42 * 6) (RQ s) = true ∧
    invTab 42 repT[s]! = unpack 42 6 (pinvS 42 6 (mask 6) (RQ s)) ∧
    canonK 42 6 (mask 6) (42 * 6) (pinvS 42 6 (mask 6) (RQ s)) = true ∧
    pcomp 42 6 (mask 6) (RQ s) (pinvS 42 6 (mask 6) (RQ s)) = pidn 42 6 := by
  obtain ⟨b1, b2⟩ := andB_iff.1 (allN' kRep2005 s hs)
  obtain ⟨c, b3⟩ := andB_iff.1 b2
  obtain ⟨ci, b4⟩ := andB_iff.1 b3
  have e := Nat.eq_of_beq_eq_true b4
  have er : repT[s]! = unpack 42 6 (RQ s) := by rw [Nat.eq_of_beq_eq_true b1]; exact hrepK s hs
  exact ⟨er, c, by rw [er]; exact invTab_eq_of_pcomp c ci e, ci, e⟩

theorem hON {s : Nat} (hs : s < 8) : ON s ≤ 400 := by
  match s, hs with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide
  | 6, _ => decide
  | 7, _ => decide

theorem pinC {s : Nat} (hs : s < 8) : PinO 42 6 gensS repT[s]! 400 3 (ON s) 11 (RQ s) L34R.G GI
    (OT s) (OE s) (OS s) (OSI s) := ⟨bindS.1, bindS.2, (hrep hs).1, orbCAll s hs, hON hs⟩

theorem orbS_eq {s : Nat} (hs : s < 8) : (orbS repT[s]!).tabs = pts 42 6 (ON s) (OT s) := by
  unfold orbS gensSInv
  exact (orbit_sound (pinC hs)).1

theorem cover_refine {OA OB : Array (Array Tab)} {ER : Array Tab}
    (h : coverOK 42 ER OA = true)
    (hr : ∀ o < OA.size, ∀ x, found (indexOf OA[o]!) OA[o]! x = true →
      ∃ s < OB.size, found (indexOf OB[s]!) OB[s]! x = true) :
    coverOK 42 ER OB = true := by
  unfold coverOK at h ⊢
  dsimp only at h ⊢
  rw [CFSG.KS.BfsReplay.allBelow_iff] at h ⊢
  intro k hk
  have h' := h k hk
  simp only [Bool.or_eq_true] at h' ⊢
  rcases h' with (a | b) | c
  · exact Or.inl (Or.inl a)
  · exact Or.inl (Or.inr b)
  · right
    rw [anyBelow_iff] at c ⊢
    obtain ⟨o, ho, hf⟩ := c
    rw [map_get _ ho] at hf
    obtain ⟨s, hs, hf'⟩ := hr o ho _ hf
    exact ⟨s, hs, by rw [map_get _ hs]; exact hf'⟩

theorem coverR : coverOK 42 (pts 42 6 241920 L34R.T)
    #[pts 42 6 315 (L34O.T 0), pts 42 6 360 (L34O.T 1), pts 42 6 1008 (L34O.T 2),
      pts 42 6 280 (L34O.T 3)] = true :=
  (rpass_sound bindS (fun k hk => cnG (by omega)) hOA pinR.canon (by decide) L34R.rpAll).2

theorem cover_true : coverOK 42 (enumBFS 42 gTabs 241920).tabs
    (repT.map fun x => (orbS x).tabs) = true := by
  rw [hR.1]
  refine cover_refine coverR fun o ho x hx => ?_
  have ho' : o < 4 := ho
  rw [hOA.2 o ho', CFSG.KS.PEnum.found_indexOf_iff, size_pts] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  rw [pts_get' hj]
  have h := allN' (allN' kCov2005 o ho') j hj
  rw [strictB_app, strictB_app, strictB_app] at h
  obtain ⟨h1, h2⟩ := andB_iff.1 h
  obtain ⟨h2, h3⟩ := andB_iff.1 h2
  have hs : Nat.shiftRight (W o j) 9 < 8 := Nat.le_of_ble_eq_true h1
  have hsz : repT.size = 8 := rfl
  have hs' : Nat.shiftRight (W o j) 9 < repT.size := by rw [hsz]; exact hs
  refine ⟨Nat.shiftRight (W o j) 9, by rw [Array.size_map]; exact hs', ?_⟩
  rw [map_get _ hs', orbS_eq hs]
  exact found_pts (Nat.le_of_ble_eq_true h2) (Nat.eq_of_beq_eq_true h3)

theorem cosetCheck_true : cosetCheck (enumBFS 42 gensS 20160).tabs
    (enumBFS 42 gTabs 241920).tabs = true := by
  unfold cosetCheck
  simp only [Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨?_, cover_true⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [CFSG.KS.BfsReplay.allBelow_iff]
    intro i hi
    have hi' : i < 8 := hi
    unfold orbS gensSInv
    exact (orbit_sound (pinC hi')).2
  · rw [hS.1, CFSG.KS.BfsReplay.allBelow_iff]
    intro i hi
    rw [CFSG.KS.BfsReplay.allBelow_iff]
    intro j hj
    have hi' : i < 8 := hi
    have hj' : j < 8 := hj
    have h := notRowAll i hi'
    unfold notRow at h
    rw [strictB_app] at h
    have h' := allN' h j hj'
    have esT : sT = L34S.T := rfl
    rw [esT] at h'
    obtain ⟨-, -, ei, ci, -⟩ := hrep hi'
    obtain ⟨ej, cj, -⟩ := hrep hj'
    rcases orB_iff.1 h' with h1 | h1
    · rw [Bool.or_eq_true, beq_iff_eq]
      exact Or.inl (Nat.eq_of_beq_eq_true h1)
    · rw [Bool.or_eq_true]
      right
      rw [ei, ej, comp_unpack' ci cj]
      exact notIn_sound rfl (cn ci cj) pinS.canon h1
  · rw [CFSG.KS.BfsReplay.allBelow_iff]
    intro i hi
    have hi' : i < 8 := hi
    obtain ⟨er, c, ei, ci, e⟩ := hrep hi'
    rw [ei, er, size_unpack, comp_inv_of_pcomp c ci e]
    simp
  · rw [eg4i, size_unpack]
    rfl
  · rw [eg4i, e4, comp_inv_of_pcomp (cnG (by decide)) cGI3 eGI3]
    exact beq_self_eq_true _

end CertificateChecks.KernelLC.L34Cos

end
