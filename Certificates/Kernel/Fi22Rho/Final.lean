module

public import Certificates.Kernel.Fi22Rho.Data
public import CFSG.Certificates.Kernel.Spor.RelTR
public import CFSG.Certificates.Kernel.Fi22.LettersSound
import Certificates.Kernel.Fi22Rho.Checks
import Certificates.Kernel.Fi22Core.OrbData
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelFi22Rho

open CFSG.KC.Enum CFSG.KS CFSG.KS.TW CFSG.KS.Fi22L CFSG.KS.RelTR CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Bridge.TwoGen.Native CFSG.Sporadic.Fi22.Native
  CFSG.Sporadic.Recognition.Fi22Multiplier

@[expose] noncomputable def F : Nat × Bool → Nat → Nat :=
  letterF (reg ljPacked 0) (reg ljPacked 0) (reg ljPacked 1) (reg ljPacked 2)

theorem hL (l : Nat × Bool) :
    TR 3510 (letterTab orbL.alpha orbL.alpha orbL.beta (invT 3510 orbL.beta) l) (F l) :=
  letterTab_TR (tr_alpha CertificateChecks.KernelFi22.Letters.gen_ok)
    (tr_alpha CertificateChecks.KernelFi22.Letters.gen_ok)
    (tr_beta CertificateChecks.KernelFi22.Letters.gen_ok)
    (tr_binv CertificateChecks.KernelFi22.Letters.gen_ok) l

theorem F_lt (l : Nat × Bool) {y : Nat} (hy : y < 3510) : F l y < 3510 := ((hL l).2 y hy).2

theorem wordF_lt (w : List (Nat × Bool)) {y : Nat} (hy : y < 3510) : wordF F w y < 3510 := by
  induction w with
  | nil => exact hy
  | cons l w ih => exact F_lt l ih

theorem reg_lk {t : Nat} (ht : t < 2) (y : Nat) : reg ljPacked t y = lk (orbT t) y := by
  unfold reg
  rw [regT_lt ht]

theorem appK_eq (l : Nat × Bool) (y : Nat) : appK l y = F l y := by
  obtain ⟨i, b⟩ := l
  unfold appK F letterF
  by_cases hi : i = 0
  · subst hi
    cases b <;> exact (reg_lk (by norm_num) y).symm
  · have e : Nat.beq i 0 = false := by
      rw [Bool.eq_false_iff]
      intro h
      exact hi (Nat.eq_of_beq_eq_true h)
    rw [e, if_neg hi]
    cases b
    · rfl
    · exact (reg_lk (by norm_num) y).symm

theorem wordK_eq (w : List (Nat × Bool)) (y : Nat) : wordK w y = wordF F w y := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    change strictN (wordK w y) (fun z => appK l z) = F l (wordF F w y)
    rw [Raw.Orb.strictN_eq, ih, appK_eq]

theorem nt_eq {c : Nat} (hc : c < 9) {x : Nat} (hx : x < 3510) :
    nt c x = wordF F (fi22Letter c) x := by
  have hs : 6 * c + x / 585 < 54 := by omega
  have h := nodeAll (6 * c + x / 585) hs
  unfold nodeSl at h
  have e1 : Nat.div (6 * c + x / 585) 6 = c := by
    change (6 * c + x / 585) / 6 = c
    omega
  have e2 : Nat.mul (Nat.mod (6 * c + x / 585) 6) 585 = x / 585 * 585 := by
    change (6 * c + x / 585) % 6 * 585 = x / 585 * 585
    congr 1
    omega
  rw [Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, e1, e2] at h
  have h' := allN_spec h (x % 585) (Nat.mod_lt _ (by norm_num))
  have e3 : Nat.add (x / 585 * 585) (x % 585) = x := by
    change x / 585 * 585 + x % 585 = x
    omega
  rw [e3] at h'
  rw [Nat.eq_of_beq_eq_true h', wordK_eq]

theorem expand_eq : ∀ w : List Nat, (∀ c ∈ w, c < 9) → ∀ {y : Nat}, y < 3510 →
    wordF F (expandWord w) y = wordN w y
  | [], _, _, _ => rfl
  | c :: w, hw, y, hy => by
    have ih := expand_eq w (fun d hd => hw d (List.mem_cons_of_mem c hd)) hy
    have e : expandWord (c :: w) = fi22Letter c ++ expandWord w := by
      unfold expandWord
      rw [List.flatMap_cons]
    change wordF F (expandWord (c :: w)) y = strictN (wordN w y) fun z => nt c z
    rw [e, wordF_append, Raw.Orb.strictN_eq, ih,
      nt_eq (hw c List.mem_cons_self) (by rw [← ih]; exact wordF_lt _ hy)]

theorem relAt_fix {r : Nat} (hr : r < 48) {x : Nat} (hx : x < 3510) : relAtN r x = x := by
  have hs : 6 * r + x / 585 < 288 := by omega
  have h := relAll (6 * r + x / 585) hs
  unfold relSl at h
  have e1 : Nat.div (6 * r + x / 585) 6 = r := by
    change (6 * r + x / 585) / 6 = r
    omega
  have e2 : Nat.mul (Nat.mod (6 * r + x / 585) 6) 585 = x / 585 * 585 := by
    change (6 * r + x / 585) % 6 * 585 = x / 585 * 585
    congr 1
    omega
  rw [Raw.Orb.strictB_eq, Raw.Orb.strictB_eq, e1, e2] at h
  have h' := allN_spec h (x % 585) (Nat.mod_lt _ (by norm_num))
  have e3 : Nat.add (x / 585 * 585) (x % 585) = x := by
    change x / 585 * 585 + x % 585 = x
    omega
  rw [e3] at h'
  exact Nat.eq_of_beq_eq_true h'

theorem relAt_lt {r : Nat} (hr : r < 47) (y : Nat) :
    relAtN r y = wordN (List.getD nodeRels r []) y := by
  unfold relAtN
  have e : Nat.blt r 47 = true := Nat.blt_eq.mpr hr
  rw [e]

theorem relAt_last (y : Nat) : relAtN 47 y = wordN fi22BWord (reg ljPacked 2 y) := rfl

theorem nodeRels_lt : ∀ w ∈ nodeRels, ∀ c ∈ w, c < 9 := by decide +kernel

theorem bword_lt : ∀ c ∈ fi22BWord, c < 9 := by decide +kernel

theorem nodeRels_len : nodeRels.length = 47 := by decide +kernel

theorem yRels_len : (CFSG.YGroups.yRels 3 3 2).length = 46 := by decide +kernel

theorem rho_check : fi22RelCheck fi22RhoRels = true := by
  unfold fi22RelCheck
  rw [CertificateChecks.KernelFi22C.orbitData_eq]
  refine relCheck_of_TR (by norm_num) hL ?_
  intro v hv x hx
  unfold fi22RhoRels at hv
  rcases List.mem_append.1 hv with h | h
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h
    obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.1 hw
    have hr' : r < 46 := by rw [← yRels_len]; exact hr
    have hm : (CFSG.YGroups.yRels 3 3 2)[r] ∈ nodeRels :=
      List.mem_append_left _ (List.getElem_mem hr)
    have eg : List.getD nodeRels r [] = (CFSG.YGroups.yRels 3 3 2)[r] := by
      rw [nodeRels, List.getD_eq_getElem?_getD, List.getElem?_append_left hr,
        List.getElem?_eq_getElem hr]
      rfl
    exact calc wordF F (expandWord (CFSG.YGroups.yRels 3 3 2)[r]) x
        = wordN (CFSG.YGroups.yRels 3 3 2)[r] x := expand_eq _ (nodeRels_lt _ hm) hx
      _ = relAtN r x := by rw [relAt_lt (by omega), eg]
      _ = x := relAt_fix (by omega) hx
  · rcases List.mem_pair.1 h with rfl | rfl
    · have hm : f332Word ∈ nodeRels := List.mem_append_right _ (List.mem_singleton_self _)
      have eg : List.getD nodeRels 46 [] = f332Word := by decide +kernel
      exact calc wordF F (expandWord f332Word) x
          = wordN f332Word x := expand_eq _ (nodeRels_lt _ hm) hx
        _ = relAtN 46 x := by rw [relAt_lt (by norm_num), eg]
        _ = x := relAt_fix (by norm_num) hx
    · have hb : reg ljPacked 2 x < 3510 := ((hL (1, false)).2 x hx).2
      exact calc wordF F (expandWord fi22BWord ++ [(1, false)]) x
          = wordF F (expandWord fi22BWord) (reg ljPacked 2 x) := wordF_append _ _ _ _
        _ = wordN fi22BWord (reg ljPacked 2 x) := expand_eq _ bword_lt hb
        _ = relAtN 47 x := (relAt_last x).symm
        _ = x := relAt_fix (by norm_num) hx

end CertificateChecks.KernelFi22Rho

end
