module

public import Certificates.Kernel.SporSch.Ru.C2253P
public import CFSG.Certificates.Kernel.BfsPinSound
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporRuGoodInputs
meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporRuGoodInputs
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BfsPinUnpack

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuGd

open CFSG.QuasithinUnique.Vol2Native.L239.RuPairs

meta def wbM : Array Nat := ruWC [1, 1, 2]

meta def wnM : Array Nat := ruWN [1, 2]

end CertificateChecks.KernelSporSch.RuGd

#ks_perm CertificateChecks.KernelSporSch.RuGd.WB 12 CertificateChecks.KernelSporSch.RuGd.wbM
#ks_perm CertificateChecks.KernelSporSch.RuGd.WN 12 CertificateChecks.KernelSporSch.RuGd.wnM
#ks_perm CertificateChecks.KernelSporSch.RuGd.B 12 CFSG.QuasithinUnique.Vol2Native.L239.RuPairs.ruBCA
#ks_perm CertificateChecks.KernelSporSch.RuGd.CC 12 CFSG.QuasithinUnique.Vol2Native.L239.RuPairs.ruCCA
#ks_perm CertificateChecks.KernelSporSch.RuGd.XC 12 CFSG.QuasithinUnique.Vol2Native.L239.RuPairs.ruXCA
#ks_perm CertificateChecks.KernelSporSch.RuGd.CN 12 CFSG.QuasithinUnique.Vol2Native.L239.RuPairs.ruCNA
#ks_perm CertificateChecks.KernelSporSch.RuGd.XN 12 CFSG.QuasithinUnique.Vol2Native.L239.RuPairs.ruXNA

namespace CertificateChecks.KernelSporSch.RuGd

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.BfsPin
  CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.QuasithinUnique.Vol2Native.L239.RuPairs CertificateChecks.KernelSporSch
  CertificateChecks.KernelSporSch.RuG CertificateChecks.KernelSporSch.RuCe CFSG.KC.Misc.RuInv

abbrev C (p : Nat) : Prop := canonK 4060 12 (mask 12) (4060 * 12) p = true

@[expose] noncomputable def pc (p q : Nat) : Nat := pcomp 4060 12 (mask 12) p q

@[expose] noncomputable def pinv (p : Nat) : Nat := pinvS 4060 12 (mask 12) p

@[expose] noncomputable def okI (p : Nat) : Bool :=
  bAnd(canonK 4060 12 (mask 12) (4060 * 12) p, bAnd(canonK 4060 12 (mask 12) (4060 * 12) (pinv p),
    pk p (pinv p)))

@[expose] noncomputable def pe (p e r : Nat) : Bool :=
  powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) p e r

@[expose] noncomputable def ne1 (p : Nat) : Bool :=
  neIdK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) p

theorem cu {p q : Nat} (hp : C p) (hq : C q) :
    compA 4060 (unpack 4060 12 p) (unpack 4060 12 q) = unpack 4060 12 (pc p q) :=
  compA_unpack hp hq

theorem cc {p q : Nat} (hp : C p) (hq : C q) : C (pc p q) := canonK_pcomp hp hq

theorem okI_spec {a : Array Nat} {p : Nat} (ha : a = unpack 4060 12 p) (h : okI p = true) :
    C p ∧ C (pinv p) ∧ ruInv a = unpack 4060 12 (pinv p) ∧ isInvA 4060 a (ruInv a) = true := by
  unfold okI at h
  obtain ⟨h1, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨h2, h3⟩ := (bAnd_iff _ _).1 h
  exact ⟨h1, h2, inv_of ha h3⟩

theorem hWB : wordEqK 4060 12 (mask 12) (pidn 4060 12) (gen2 C0 C1) (gen2 C0I C1I) 2 [1, 1, 2] WB =
    true := by quickRfl
theorem hWN : wordEqK 4060 12 (mask 12) (pidn 4060 12) (gen2 Ns0 Ns1) (gen2 Ns0I Ns1I) 2 [1, 2] WN =
    true := by quickRfl

theorem wb_eq : ruWC [1, 1, 2] = unpack 4060 12 WB := by
  unfold ruWC
  exact (congrArg (fun T => wordA 4060 #[ruC0A, ruC1A] T [1, 1, 2]) (invs2 ruC0A ruC1A)).trans
    (wordEqK_sound (binds2 c0_eq c1_eq) (perms2 pC0 pC1) hWB).1

theorem wn_eq : ruWN [1, 2] = unpack 4060 12 WN := by
  unfold ruWN
  exact (congrArg (fun T => wordA 4060 #[ruNs0A, ruNs1A] T [1, 2]) (invs2 ruNs0A ruNs1A)).trans
    (wordEqK_sound (binds2 ns0_eq ns1_eq) (perms2 pNs0 pNs1) hWN).1

theorem pB : pe WB 2 B = true := by quickRfl
theorem pCC : pe C0 4 CC = true := by quickRfl
theorem pCN : pe WN 2 CN = true := by quickRfl

theorem b_eq : ruBCA = unpack 4060 12 B := by
  unfold ruBCA
  rw [wb_eq]
  exact powEqRK_sound pB

theorem cc_eq : ruCCA = unpack 4060 12 CC := by
  unfold ruCCA
  rw [c0_eq]
  exact powEqRK_sound pCC

theorem cn_eq : ruCNA = unpack 4060 12 CN := by
  unfold ruCNA
  rw [wn_eq]
  exact powEqRK_sound pCN

theorem oB : okI B = true := by quickRfl
theorem oJ : okI (JG 0) = true := by quickRfl
theorem oK : okI (KG 0) = true := by quickRfl
theorem oCN : okI CN = true := by quickRfl
theorem cCC : C CC := by quickRfl
theorem cNs1 : C Ns1 := by quickRfl
theorem cNs1I : C Ns1I := by quickRfl
theorem cXC : C XC := by quickRfl
theorem cXN : C XN := by quickRfl

theorem j_eq : ruJGensA[0]! = unpack 4060 12 (JG 0) := jg_eq (by norm_num)
theorem k_eq : ruKGensA[0]! = unpack 4060 12 (KG 0) := kg_eq (by norm_num)

theorem eXC : Nat.beq (pc (pc (pc (JG 0) B) (pinv (JG 0))) (pinv B)) XC = true := by quickRfl
theorem eXN : Nat.beq (pc (pc (pc (KG 0) Ns1) (pinv (KG 0))) Ns1I) XN = true := by quickRfl

theorem xc_eq : ruXCA = unpack 4060 12 XC := by
  obtain ⟨j, ji, ij, -⟩ := okI_spec j_eq oJ
  obtain ⟨b, bi, ib, -⟩ := okI_spec b_eq oB
  unfold ruXCA
  rw [ij, ib, j_eq, b_eq, cu j b, cu (cc j b) ji, cu (cc (cc j b) ji) bi, Nat.eq_of_beq_eq_true eXC]

theorem xn_eq : ruXNA = unpack 4060 12 XN := by
  obtain ⟨k, ki, ik, -⟩ := okI_spec k_eq oK
  have is1 := (inv_of ns1_eq pNs1).1
  unfold ruXNA
  rw [ik, is1, k_eq, ns1_eq, cu k cNs1, cu (cc k cNs1) ki, cu (cc (cc k cNs1) ki) cNs1I,
    Nat.eq_of_beq_eq_true eXN]

theorem b3 : pe B 3 (pidn 4060 12) = true := by quickRfl
theorem c5 : pe CC 5 (pidn 4060 12) = true := by quickRfl
theorem s3 : pe Ns1 3 (pidn 4060 12) = true := by quickRfl
theorem n7 : pe CN 7 (pidn 4060 12) = true := by quickRfl
theorem bNe : ne1 B = true := by quickRfl
theorem cNe : ne1 CC = true := by quickRfl
theorem sNe : ne1 Ns1 = true := by quickRfl
theorem nNe : ne1 CN = true := by quickRfl
theorem xcNe : ne1 (pc XC XC) = true := by quickRfl
theorem xnNe : ne1 (pc XN XN) = true := by quickRfl
theorem jcNe : neK 4060 12 (mask 12) (4060 * 12) (pc (JG 0) CC) (pc CC (JG 0)) = true := by quickRfl
theorem knNe : neK 4060 12 (mask 12) (4060 * 12) (pc (KG 0) CN) (pc CN (KG 0)) = true := by quickRfl

theorem pow_one {a : Array Nat} {p e : Nat} (ha : a = unpack 4060 12 p)
    (h : pe p e (pidn 4060 12) = true) : eqA 4060 (powA 4060 a e) (idA 4060) = true := by
  rw [ha, powEqRK_sound h, ← idK_sound idOK]
  exact eqA_unpack_self _ _ _

theorem facts :
    (isInvA 4060 ruBCA (ruInv ruBCA) = true ∧
      isInvA 4060 ruJGensA[0]! (ruInv ruJGensA[0]!) = true ∧
      eqA 4060 (powA 4060 ruBCA 3) (idA 4060) = true ∧ eqA 4060 ruBCA (idA 4060) = false ∧
      eqA 4060 (powA 4060 ruCCA 5) (idA 4060) = true ∧ eqA 4060 ruCCA (idA 4060) = false ∧
      eqA 4060 (compA 4060 ruXCA ruXCA) (idA 4060) = false ∧
      eqA 4060 (compA 4060 ruJGensA[0]! ruCCA) (compA 4060 ruCCA ruJGensA[0]!) = false) ∧
    (isInvA 4060 ruKGensA[0]! (ruInv ruKGensA[0]!) = true ∧
      eqA 4060 (powA 4060 ruNs1A 3) (idA 4060) = true ∧ eqA 4060 ruNs1A (idA 4060) = false ∧
      isInvA 4060 ruCNA (ruInv ruCNA) = true ∧
      eqA 4060 (powA 4060 ruCNA 7) (idA 4060) = true ∧ eqA 4060 ruCNA (idA 4060) = false ∧
      eqA 4060 (compA 4060 ruXNA ruXNA) (idA 4060) = false ∧
      eqA 4060 (compA 4060 ruKGensA[0]! ruCNA) (compA 4060 ruCNA ruKGensA[0]!) = false) := by
  have j := (okI_spec j_eq oJ).1
  have k := (okI_spec k_eq oK).1
  have n := (okI_spec cn_eq oCN).1
  refine ⟨⟨(okI_spec b_eq oB).2.2.2, (okI_spec j_eq oJ).2.2.2, pow_one b_eq b3, ?_,
    pow_one cc_eq c5, ?_, ?_, ?_⟩, ⟨(okI_spec k_eq oK).2.2.2, pow_one ns1_eq s3, ?_,
    (okI_spec cn_eq oCN).2.2.2, pow_one cn_eq n7, ?_, ?_, ?_⟩⟩
  · rw [b_eq]
    exact neIdK_sound bNe
  · rw [cc_eq]
    exact neIdK_sound cNe
  · rw [xc_eq, cu cXC cXC]
    exact neIdK_sound xcNe
  · rw [j_eq, cc_eq, cu j cCC, cu cCC j]
    exact neK_sound jcNe
  · rw [ns1_eq]
    exact neIdK_sound sNe
  · rw [cn_eq]
    exact neIdK_sound nNe
  · rw [xn_eq, cu cXN cXN]
    exact neIdK_sound xnNe
  · rw [k_eq, cn_eq, cu k n, cu n k]
    exact neK_sound knNe

end CertificateChecks.KernelSporSch.RuGd

end
