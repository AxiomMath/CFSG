module

public import Certificates.Kernel.Sporadic.Fi24Seven.Light
public import Certificates.Kernel.Sporadic.Fi24Seven.Text
public import CFSG.Certificates.Kernel.Spor.Fi24SlpSound
public import CFSG.Certificates.Kernel.Spor.SlpTextSound
public import Certificates.Kernel.Sporadic.Fi24Ext.Decoded
import Certificates.Kernel.Sporadic.Fi24Br.K

public section

namespace CertificateChecks.KernelF24S

open CFSG.KC.SlpM CFSG.KD.F24S CFSG.KS.Mat3 CFSG.KC.Ord CFSG.Sporadic.Fi24.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24SevenNative CFSG.HardMathSupport.Dickson.I271.Fi7

theorem cn_B2 : Canon3 609961 (R 0) ∧
    mat3 781 609961 (R 0) = mat3 781 609961 (CFSG.KD.BrFi24.RB 24) * mat3 781 609961 (CFSG.KD.BrFi24.RB 24) := by
  have e : CFSG.KD.BrFi24.MUL (CFSG.KD.BrFi24.RB 24) (CFSG.KD.BrFi24.RB 24) = R 0 :=
    Nat.eq_of_beq_eq_true b2_ok
  have := KernelFi24Ext.mul_mt KernelFi24Ext.cn_B KernelFi24Ext.cn_B
  rw [e] at this
  exact this

theorem wl_cases (l : Nat) : WL l = W7 ∨ WL l = appL W7 E7 ∨ WL l = appL W7 EK := by
  unfold WL
  cases Nat.beq l 0 <;> cases Nat.beq l 1
  · exact Or.inr (Or.inr rfl)
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl rfl
  · exact Or.inl rfl

theorem w7_len : W7.length = 1087 := by
  have := Nat.eq_of_beq_eq_true len7
  rwa [lenL_eq] at this

theorem e7_len : E7.length = 119 := by
  have := Nat.eq_of_beq_eq_true lenE7
  rwa [lenL_eq] at this

theorem ek_len : EK.length = 2733 := by
  have := Nat.eq_of_beq_eq_true lenEK
  rwa [lenL_eq] at this

theorem c7_len : C7.length = 343 := by
  have := Nat.eq_of_beq_eq_true lenC7
  rwa [lenL_eq] at this

theorem semN_append {M : Type*} [Monoid M] (g : Int → M) (E : List (List Nat)) {n : Nat}
    (hn : n < 2174) : semN g (appL W7 E) n = semN g W7 n := by
  unfold semN
  rw [appL_eq, List.map_append, ← List.append_toArray, semArr_append_getD]
  simp [w7_len]
  omega

theorem semN_base {M : Type*} [Monoid M] (g : Int → M) (l : Nat) {n : Nat} (hn : n < 2174) :
    semN g (WL l) n = semN g W7 n := by
  rcases wl_cases l with e | e | e <;> rw [e]
  · exact semN_append g E7 hn
  · exact semN_append g EK hn

theorem gen_eq : gen3 (mat3 781 609961 (CFSG.KD.BrFi24.RB 23)) (mat3 781 609961 (CFSG.KD.BrFi24.RB 24)) =
    gW := by
  have hA : mat3 781 609961 (CFSG.KD.BrFi24.RB 23) = matW 781 781 (matA ()) := KernelFi24Ext.A_mt
  have hB : mat3 781 609961 (CFSG.KD.BrFi24.RB 24) = matW 781 781 (matB ()) := KernelFi24Ext.B_mt
  rw [hA, hB]

theorem facts {K nRr : Nat} (hk : ∀ k < K, CK k = true)
    (hp : planOK K nRr nBase lyK pcR pnR inK ouK = true) :
    ∀ k < K, (∀ e ∈ eqK k, semE gW (WL (lyK k)) e.1 = semE gW (WL (lyK k)) e.2) ∧
      ∀ e ∈ neK k, semE gW (WL (lyK k)) e.1 ≠ semE gW (WL (lyK k)) e.2 := by
  have := (slp_records (d := 781) (f := 11) CFSG.KD.BrFi24.consts
    ⟨KernelFi24Ext.cn_A, rfl⟩ ⟨KernelFi24Ext.cn_B, rfl⟩ cn_B2 (WL := WL) (base := 2174)
    (fun l l' n hn => by rw [semN_base _ l hn, semN_base _ l' hn]) (K := K) (nR := nRr) (R := R)
    (LY := lyK) (PC := pcR) (PN := pnR) (IN := inK) (OU := ouK) (ND := ndK) (EQ := eqK) (NE := neK)
    (fun k h => hk k h) hp).2
  rw [gen_eq] at this
  exact this

theorem eq_of_has {K nRr l : Nat} (hk : ∀ k < K, CK k = true)
    (hp : planOK K nRr nBase lyK pcR pnR inK ouK = true) {e : List Nat × List Nat}
    (h : hasEq lyK eqK K l e = true) : semE gW (WL l) e.1 = semE gW (WL l) e.2 := by
  obtain ⟨k, hkK, hl, he⟩ := hasEq_spec h
  have := (facts hk hp k hkK).1 e he
  rwa [hl] at this

theorem ne_of_has {K nRr l : Nat} (hk : ∀ k < K, CK k = true)
    (hp : planOK K nRr nBase lyK pcR pnR inK ouK = true) {e : List Nat × List Nat}
    (h : hasEq lyK neK K l e = true) : semE gW (WL l) e.1 ≠ semE gW (WL l) e.2 := by
  obtain ⟨k, hkK, hl, he⟩ := hasEq_spec h
  have := (facts hk hp k hkK).2 e he
  rwa [hl] at this

theorem words_eq : fi24SevenData.words = (W7.map decW).toArray := by
  change parseIntLists words7 = _
  rw [words7_txt]
  exact parseIntLists_wordsC (List.ne_nil_of_length_pos (by rw [w7_len]; omega))

theorem conj_eq : fi24SevenData.conj = C7.toArray := by
  change parsePairs conj7 = _
  rw [conj7_txt]
  exact parsePairs_pairsC (List.ne_nil_of_length_pos (by rw [c7_len]; omega))

theorem extra7_eq : fi7Extra () = (E7.map decW).toArray := by
  change parseIntLists fi7ExtraStr = _
  rw [fi7Extra_txt]
  exact parseIntLists_wordsC (List.ne_nil_of_length_pos (by rw [e7_len]; omega))

theorem extraK_eq : CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.fi24kExtra () = (EK.map decW).toArray := by
  change parseIntLists CFSG.LocalAnalysis.RankThreeTheoremC.Fi24K.fi24kExtraStr = _
  rw [fi24kExtra_txt]
  exact parseIntLists_wordsC (List.ne_nil_of_length_pos (by rw [ek_len]; omega))

theorem decC_even {c j : Nat} (hc : c = 2 * j) : decC c = (j : Int) := by
  subst hc
  unfold decC
  rw [if_neg (by omega)]
  congr 1
  omega

theorem decC_odd {c j : Nat} (hc : c = 2 * j + 1) : decC c = -(j : Int) := by
  subst hc
  unfold decC
  rw [if_pos (by omega)]
  congr 2
  omega

theorem layer_words (E : List (List Nat)) :
    (W7.map decW).toArray ++ (E.map decW).toArray = ((appL W7 E).map decW).toArray := by
  rw [appL_eq, List.map_append, List.append_toArray]

end CertificateChecks.KernelF24S

end
