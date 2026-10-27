module

public import Certificates.Kernel.Sporadic.Fi24F4.JGlue
public import Certificates.Kernel.Sporadic.Fi24F4.SC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicFi24TwoBJFacts
public import CFSG.Certificates.Kernel.Spor.Fi24F4WSound
public import Certificates.Kernel.Sporadic.Fi24Base.Glue
public import Certificates.Kernel.Sporadic.Fi24F4.JInd
public import Certificates.Kernel.Sporadic.Fi24F4.RowP

public section

namespace CFSG.KD.Fi24F4

open CFSG.KC CFSG.KC.Fi24R2W CFSG.KC.Fi24F4J CFSG.KD.Fi24Net CFSG.KS.Fi24Kit CFSG.KS.Fi24Net
open CFSG.Sporadic.Fi24I301 CFSG.Sporadic.FischerOddCore CFSG.Sporadic.Th
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
open CertificateChecks.KernelSpor.Fi24R2W CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.Sporadic.Fi24 (J tR)
open CertificateChecks.KernelSpor.Fi24F4 (card_N_centralizer card_P_centralizer)
open Finset

attribute [local instance] CFSG.Sporadic.Fi24.rAction

theorem base_lt' : ∀ m, nthV base m < 306936
  | 0 => by decide
  | 1 => by decide
  | 2 => by decide
  | 3 => by decide
  | 4 => by decide
  | 5 => by decide
  | m + 6 => (by norm_num : (0 : ℕ) < 306936)

theorem card_subtype_fin_eq' (n : ℕ) (q : ℕ → Prop) [DecidablePred q] :
    Nat.card {k : Fin n // q k.val} = ((range n).filter q).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← card_map Fin.valEmbedding]
  congr 1
  ext i
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨hi, hq⟩
    exact ⟨⟨i, hi⟩, hq, rfl⟩

theorem prodW_lt {X : List (List ℕ)} (hX : ∀ i < 5, ∀ l ∈ nthW X i, l < 26) (e : List ℕ) :
    ∀ l ∈ prodW X e, l < 26 := by
  intro l hl
  unfold prodW at hl
  simp only [List.mem_append] at hl
  rcases hl with h | h | h | h | h
  · exact repL_lt (hX 0 (by norm_num)) _ l h
  · exact repL_lt (hX 1 (by norm_num)) _ l h
  · exact repL_lt (hX 2 (by norm_num)) _ l h
  · exact repL_lt (hX 3 (by norm_num)) _ l h
  · exact repL_lt (hX 4 (by norm_num)) _ l h

theorem indc_all : ∀ n, 0 < n → n < 243 → indc n = true := by
  intro n h0 hn
  have hs : n / 81 < 3 := by omega
  have h := CFSG.KS.allN_spec (show indS (n / 81) = true by
    interval_cases (n / 81)
    exacts [Ck.indS0, Ck.indS1, Ck.indS2]) (n % 81) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (n / 81) 81) (n % 81) = n := by
    change n / 81 * 81 + n % 81 = n
    omega
  rw [e] at h
  have hb : Nat.beq n 0 = false := by
    cases hb : Nat.beq n 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) (by omega)
  rw [hb] at h
  exact h

theorem sx_lt : ∀ i < 5, ∀ l ∈ nthW J.sx i, l < 26 := fun i hi => (codes_ok.1 i hi).2.2

theorem xJ_pow_prodW (e : List ℕ) :
    prodC (prodW J.sx e) = xJ 0 ^ nthV e 0 * (xJ 1 ^ nthV e 1 * (xJ 2 ^ nthV e 2 *
      (xJ 3 ^ nthV e 3 * xJ 4 ^ nthV e 4))) := by
  rw [prodC_prodW, xJ_eq (by norm_num : 0 < 5), xJ_eq (by norm_num : 1 < 5),
    xJ_eq (by norm_num : 2 < 5), xJ_eq (by norm_num : 3 < 5), xJ_eq (by norm_num : 4 < 5)]

theorem card_fixedBy_x0 : Nat.card (MulAction.fixedBy (Fin 306936) (xJ 0)) = 3240 := by
  have hw := sx_lt 0 (by norm_num)
  have hfix := CFSG.KS.Fi24FixP.fixOK_spec (σ := LN NW) (A := CFSG.KC.Fi24NetPt.planeL NW)
    (w := nthW J.sx 0) (fun l hl q hq => CFSG.KD.Fi24Base.LN_lt19 (hw l hl) hq)
    (fun l hl v q _ => CFSG.KS.Fi24NetPt.testBit_planeL (CFSG.KD.Fi24Base.nv_LN (hw l hl)) v q)
    Ck.fix
  rw [← hfix, ← card_subtype_fin_eq']
  change Nat.card {k : Fin 306936 // xJ 0 • k = k} = _
  refine Nat.card_congr (Equiv.subtypeEquivRight fun k => ?_)
  rw [xJ_eq (by norm_num : 0 < 5)]
  have e := (idx_prodC _ hw k.val k.isLt).1
  rw [idx_of_lt _ k.isLt] at e
  change _ ↔ wN NW (nthW J.sx 0) k.val = k.val
  rw [← e]
  exact ⟨fun h => by rw [h], fun h => Fin.ext h⟩

theorem rowFacts_of : RowFacts := by
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_, ?_, card_fixedBy_x0, card_N_centralizer,
    card_P_centralizer⟩
  · rw [xJ_eq hi, ← prodC_repL]
    exact eq_of_stage (repL_lt (sx_lt i hi) 3) (fun l hl => absurd hl List.not_mem_nil)
      (cubec_all i hi)
  · rw [xJ_eq hi, xJ_eq hj, ← prodC_append, ← prodC_append]
    have h := commc_all (5 * i + j) (by omega)
    unfold commc at h
    have e1 : Nat.div (5 * i + j) 5 = i := by change (5 * i + j) / 5 = i; omega
    have e2 : Nat.mod (5 * i + j) 5 = j := by change (5 * i + j) % 5 = j; omega
    rw [e1, e2] at h
    refine eq_of_stage (fun l hl => ?_) (fun l hl => ?_) h
    · rcases List.mem_append.1 hl with h' | h'
      · exact sx_lt i hi l h'
      · exact sx_lt j hj l h'
    · rcases List.mem_append.1 hl with h' | h'
      · exact sx_lt j hj l h'
      · exact sx_lt i hi l h'
  · intro i₀ i₁ i₂ i₃ i₄ h₀ h₁ h₂ h₃ h₄ hp
    by_contra hne
    set n := 81 * i₀ + 27 * i₁ + 9 * i₂ + 3 * i₃ + i₄ with hn
    have hn0 : 0 < n := by omega
    have hdig : digits3 n = [i₀, i₁, i₂, i₃, i₄] := by
      change [n / 81 % 3, n / 27 % 3, n / 9 % 3, n / 3 % 3, n % 3] = _
      simp only [List.cons.injEq, and_true]
      omega
    have h := indc_all n hn0 (by omega)
    unfold indc at h
    rw [hdig] at h
    apply moves_ne (prodW_lt sx_lt _) (base_lt' _) h
    rw [xJ_pow_prodW]
    change xJ 0 ^ i₀ * (xJ 1 ^ i₁ * (xJ 2 ^ i₂ * (xJ 3 ^ i₃ * xJ 4 ^ i₄))) = 1
    rw [← hp]
    simp only [mul_assoc]

theorem nJ_eq {k : ℕ} (hk : k < 2) : nJ k = prodC (nthW J.sn k) := by
  obtain ⟨h1, h2, -⟩ := codes_ok.2.1 k hk
  unfold nJ
  rw [nW_eq k hk, ← prodC_cw _ (letters_ok.2 k hk)]
  exact eq_of_stage h1 h2 (snc_all k hk)

theorem rows_eq : ∀ k < 2, ∀ i < 5, (nMats[k]!)[i]! = nRow k i ∧
    ∀ j < 5, (nRow k i)[j]! = nthV (nRow k i) j := by decide +kernel

theorem prodElt_eq (v : List ℕ) (hv : ∀ j < 5, v[j]! = nthV v j) :
    prodElt v = prodC (prodW J.sx v) := by
  rw [xJ_pow_prodW, ← hv 0 (by norm_num), ← hv 1 (by norm_num), ← hv 2 (by norm_num),
    ← hv 3 (by norm_num), ← hv 4 (by norm_num)]
  unfold prodElt
  simp only [show List.range 5 = [0, 1, 2, 3, 4] from rfl, List.foldl_cons, List.foldl_nil,
    one_mul, mul_assoc]

theorem coverFacts_of : CoverFacts := by
  intro k hk i hi
  obtain ⟨-, hsn, hsni⟩ := codes_ok.2.1 k hk
  obtain ⟨hr1, hr2⟩ := rows_eq k hk i hi
  rw [hr1, prodElt_eq _ hr2, nJ_eq hk, xJ_eq hi,
    ← prodC_invC, ← prodC_append, ← prodC_append]
  have h := relc_all (5 * k + i) (by omega)
  unfold relc at h
  have e1 : Nat.div (5 * k + i) 5 = k := by change (5 * k + i) / 5 = k; omega
  have e2 : Nat.mod (5 * k + i) 5 = i := by change (5 * k + i) % 5 = i; omega
  rw [e1, e2] at h
  rw [List.append_assoc]
  refine eq_of_stage (fun l hl => ?_) (prodW_lt sx_lt _) h
  rcases List.mem_append.1 hl with h' | h'
  · exact hsn l h'
  · rcases List.mem_append.1 h' with h'' | h''
    · exact sx_lt i hi l h''
    · exact hsni l h''

theorem sqc_all : ∀ e < 13, sqc e = true := by
  intro e he
  interval_cases e
  exacts [Ck.sqc0, Ck.sqc1, Ck.sqc2, Ck.sqc3, Ck.sqc4, Ck.sqc5, Ck.sqc6, Ck.sqc7, Ck.sqc8,
    Ck.sqc9, Ck.sqc10, Ck.sqc11, Ck.sqc12]

theorem qElt_eq {e : ℕ} (he : e < 13) : fi24QElt (qW.getD e ([], 0)) = prodC (nthW J.sq e) := by
  obtain ⟨h1, h2⟩ := codes_ok.2.2 e he
  unfold fi24QElt
  rw [← prodC_cwQ, ← prodC_repL]
  exact eq_of_stage (repL_lt h1 _) h2 (sqc_all e he)

theorem qe_facts : J.qe = 1 ∧ J.qb < 6 ∧ fi24QWords[0]! = qW.getD 0 ([], 0) ∧
    qW.getD 1 ([], 0) ∈ fi24QWords.tail := by decide +kernel

theorem sigma_not_mem {x : Equiv.Perm (Fin 504)}
    (hx : ∀ j : Fin 504, idx 306936 tR fi24FPts[j.val]! = fi24FPts[(x j).val]!) : x ∉ fi24K := by
  have hsig := CFSG.KS.allN_spec Ck.sig
  have hxj : ∀ j : Fin 504, (x j).val = pg 9 (mask 9) sigP j.val := by
    intro j
    obtain ⟨hl, h4⟩ := CFSG.KS.Fi24F4W.andB_iff.1 (hsig j.val j.isLt)
    obtain ⟨hp, hT⟩ := CFSG.KS.Fi24F4W.andB_iff.1 h4
    have hlt : nthV S.sig j.val < 504 := Nat.le_of_ble_eq_true hl
    have e1 := hx j
    rw [fpts_get j.isLt, fpts_get (x j).isLt] at e1
    have e2 : idx 306936 tR (fpt FP.F j.val) = fpt FP.F (nthV S.sig j.val) := by
      rw [idx_of_lt _ (fpt_lt j.isLt),
        CFSG.KD.Fi24ThreeO.Group.tR_val CertificateChecks.KernelFi24OrbL.bridge,
        ← CFSG.KS.Fi24NetPt.ptF_eq]
      exact Nat.eq_of_beq_eq_true hT
    rw [Nat.eq_of_beq_eq_true hp]
    exact fpt_inj (x j).isLt hlt (e1.symm.trans e2)
  obtain ⟨hcn, hsft⟩ := CFSG.KS.Fi24F4W.andB_iff.1 Ck.sft
  have hrep : CFSG.Monster.B.Co2.Rep 504 (unpack 504 9 sigP) x := fun j => by
    rw [CFSG.KS.Raw.Orb.unpack_get j.isLt, hxj j]
  intro hmem
  have hs := (CFSG.Certificates.siftA_iff_mem_originalSubgroup fi24KChain_arrays (by norm_num)
    fi24KChain_facts.2.1 hrep).2 hmem
  rw [CertificateChecks.KernelSpor.Fi24C.kS,
    siftK_eq CertificateChecks.KernelSpor.Fi24C.bindsK CertificateChecks.KernelSpor.Fi24C.permK
      CertificateChecks.KernelSpor.Fi24KC.hl rfl (CertificateChecks.KernelSpor.Fi24C.hi_of hcn)
      (range_of_canonK hcn)] at hs
  rw [hs] at hsft
  exact Bool.noConfusion hsft

theorem twoBJFacts_of : TwoBJFacts := by
  refine ⟨fun x hx => sigma_not_mem hx, ?_⟩
  obtain ⟨hqe, hqb, h0, h1⟩ := qe_facts
  refine ⟨qW.getD 1 ([], 0), h1, ?_⟩
  rw [h0, qElt_eq (by norm_num), qElt_eq (by norm_num), ← prodC_append, ← prodC_append]
  have h := Ck.qne
  unfold qnec at h
  rw [hqe] at h
  obtain ⟨-, h0'⟩ := codes_ok.2.2 0 (by norm_num)
  obtain ⟨-, h1'⟩ := codes_ok.2.2 1 (by norm_num)
  refine differ_ne (fun l hl => ?_) (fun l hl => ?_) (base_lt' _) h
  · rcases List.mem_append.1 hl with h' | h'
    · exact h0' l h'
    · exact h1' l h'
  · rcases List.mem_append.1 hl with h' | h'
    · exact h1' l h'
    · exact h0' l h'

end CFSG.KD.Fi24F4

end
