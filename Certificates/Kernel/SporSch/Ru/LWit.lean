module

public import Certificates.Kernel.SporSch.Ru.LData
public import Certificates.Kernel.SporSch.Ru.LFacts
public import Certificates.Kernel.SporSch.Ru.Wit
public import CFSG.Certificates.Kernel.SporSch.RuPowSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.RuLW

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG
  CertificateChecks.KernelSporSch.RuW CertificateChecks.KernelSporSch.RuLD

@[expose] noncomputable def prK (i : Nat) : Nat := nIf(Nat.beq i 0, 5, nIf(Nat.beq i 1, 7, 13))

@[expose] noncomputable def yok (i : Nat) : Bool :=
  wordEqK 4060 12 (mask 12) (pidn 4060 12) LG LGI 3 (ruObsRec (prK i)).1 (YT i)

@[expose] noncomputable def yord (i : Nat) : Bool :=
  bAnd(powEqRK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) (YT i) (prK i) (pidn 4060 12),
    neIdK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) (YT i))

@[expose] noncomputable def xok (i : Nat) : Bool :=
  bAnd(compEqK 4060 12 (mask 12) (4060 * 12) (LG 2) (YT i) (X1T i),
    bAnd(compEqK 4060 12 (mask 12) (4060 * 12) (X1T i) (LGI 2) (X2T i),
      compEqK 4060 12 (mask 12) (4060 * 12) (YT i) (X2T i) (X3T i)))

@[expose] noncomputable def qok (j : Nat) : Bool :=
  strictB (Nat.div j 13) (fun i => strictB (Nat.mod j 13) (fun q =>
    powEqRK 4060 12 (mask 12) (4060 * 12) (QT (Nat.add (Nat.mul 14 i) q)) (X3T i) 35
      (QT (Nat.add (Nat.mul 14 i) (Nat.succ q)))))

@[expose] noncomputable def wok (j : Nat) : Bool :=
  strictB (Nat.div j 8) (fun i => strictB (Nat.mod j 8) (fun q =>
    powEqRK 4060 12 (mask 12) (4060 * 12) (WT (Nat.add (Nat.mul 9 i) q))
      (QT (Nat.add (Nat.mul 14 i) 13)) 32 (WT (Nat.add (Nat.mul 9 i) (Nat.succ q)))))

@[expose] noncomputable def ends (i : Nat) : Bool :=
  bAnd(Nat.beq (QT (Nat.mul 14 i)) (pidn 4060 12), bAnd(Nat.beq (WT (Nat.mul 9 i)) (pidn 4060 12),
    bAnd(Nat.beq (WT (Nat.add (Nat.mul 9 i) 8)) (pidn 4060 12),
      neIdK 4060 12 (mask 12) (4060 * 12) (pidn 4060 12) (QT (Nat.add (Nat.mul 14 i) 13)))))

@[expose] noncomputable def lok (i : Nat) : Bool :=
  bAnd(Nat.beq (RuT4060.L (Nat.add 39 i)) (LG i), commK 4060 12 (mask 12) (4060 * 12) (LG i) A0)

end CertificateChecks.KernelSporSch.RuLW

#kss_each CertificateChecks.KernelSporSch.RuLW.YC CertificateChecks.KernelSporSch.RuLW.yok 3
#kss_each CertificateChecks.KernelSporSch.RuLW.YO CertificateChecks.KernelSporSch.RuLW.yord 3
#kss_each CertificateChecks.KernelSporSch.RuLW.XC CertificateChecks.KernelSporSch.RuLW.xok 3
#kss_each CertificateChecks.KernelSporSch.RuLW.QC CertificateChecks.KernelSporSch.RuLW.qok 39
#kss_each CertificateChecks.KernelSporSch.RuLW.WC CertificateChecks.KernelSporSch.RuLW.wok 24
#kss_each CertificateChecks.KernelSporSch.RuLW.EC CertificateChecks.KernelSporSch.RuLW.ends 3
#kss_each CertificateChecks.KernelSporSch.RuLW.LC CertificateChecks.KernelSporSch.RuLW.lok 3

namespace CertificateChecks.KernelSporSch.RuLW

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KC.Misc.RuInv
  CFSG.Sporadic.RuSchreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CertificateChecks.KernelSporSch CertificateChecks.KernelSporSch.RuG
  CertificateChecks.KernelSporSch.RuW CertificateChecks.KernelSporSch.RuLD

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem pLG : allN 3 (fun j => permOK 4060 12 (mask 12) (4060 * 12) (LG j) (LGI j)) = true := by
  quickRfl

theorem lgBinds : ruLGensA.size = 3 ∧ ∀ j < 3, ruLGensA[j]! = unpack 4060 12 (LG j) :=
  ⟨by simp [ruLGensA, ruLMWords], fun _ hj => lg_eq hj⟩

theorem lgi_eq : ruInv ruLGensA[2]! = unpack 4060 12 (LGI 2) := by
  rw [lg_eq (by omega)]
  exact (inv_of rfl (lgi (k := 2) (by omega))).1

theorem prime_cases {p : Nat} (hp : p ∈ [5, 7, 13]) : ∃ i < 3, prK i = p := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  exacts [⟨0, by omega, rfl⟩, ⟨1, by omega, rfl⟩, ⟨2, by omega, rfl⟩]

theorem y_eq {i : Nat} (hi : i < 3) : ruYpA (prK i) = unpack 4060 12 (YT i) :=
  (wordEqK_sound lgBinds pLG (YC.all i hi)).1

theorem eqA_self (P : Nat) : eqA 4060 (unpack 4060 12 P) (unpack 4060 12 P) = true :=
  eqK_sound (Nat.beq_refl P)

theorem idA_eq : idA 4060 = unpack 4060 12 (pidn 4060 12) := (idK_sound idOK).symm

theorem x3_eq {i : Nat} (hi : i < 3) :
    compA 4060 (ruYpA (prK i)) (compA 4060 (compA 4060 ruLGensA[2]! (ruYpA (prK i)))
      (ruInv ruLGensA[2]!)) = unpack 4060 12 (X3T i) := by
  obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (XC.all i hi)
  obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
  rw [lgi_eq, lg_eq (by omega), y_eq hi, compEqK_sound h1, compEqK_sound h3, compEqK_sound h4]

theorem v_eq {i : Nat} (hi : i < 3) : ruVpA (prK i) = unpack 4060 12 (QT (14 * i + 13)) := by
  have hq : ∀ q < 13, powEqRK 4060 12 (mask 12) (4060 * 12) (QT (14 * i + q)) (X3T i) 35
      (QT (14 * i + q + 1)) = true := by
    intro q hq
    have h := QC.all (13 * i + q) (by change 13 * i + q < 39; omega)
    unfold qok at h
    rw [strictB_eq', strictB_eq'] at h
    have e1 : Nat.div (13 * i + q) 13 = i := by
      change (13 * i + q) / 13 = i
      omega
    have e2 : Nat.mod (13 * i + q) 13 = q := by
      change (13 * i + q) % 13 = q
      omega
    rw [e1, e2] at h
    exact h
  have h0 : unpack 4060 12 (QT (14 * i + 0)) = idA 4060 := by
    rw [idA_eq, ← Nat.eq_of_beq_eq_true ((bAnd_iff _ _).1 (EC.all i hi)).1]
    all_goals rfl
  have := pow_chain (Q := fun q => QT (14 * i + q)) h0 hq 13 (Nat.le_refl 13)
  rw [ruVpA, x3_eq hi]
  exact this

theorem facts : ruChainOK 4060 (ruField4060 5) 3 6 ruLChainBase ruLChainDerivations = true ∧
    rawOrbitSizes 4060 (ruField4060 5) (ruBaseArr 4060 ruLChainBase) = [1820, 64] ∧
    (∀ i < 3, eqA 4060 (ruField4060 5)[i]! ruLGensA[i]! = true) ∧
    (∀ i < 3, eqA 4060 (compA 4060 ruLGensA[i]! ruA0A) (compA 4060 ruA0A ruLGensA[i]!) = true) ∧
    (∀ p ∈ [5, 7, 13], eqA 4060 (powA 4060 (ruYpA p) p) (idA 4060) = true ∧
      eqA 4060 (ruYpA p) (idA 4060) = false) ∧
    (∀ p ∈ [5, 7, 13], eqA 4060 (ruVpA p) (idA 4060) = false ∧
      eqA 4060 (powA 4060 (ruVpA p) 256) (idA 4060) = true) := by
  refine ⟨RuL.chain, RuL.orbits, fun i hi => ?_, fun i hi => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨h1, _⟩ := (bAnd_iff _ _).1 (LC.all i hi)
    rw [RuL.field_get (j := i) (by omega), RuLines.row4060 (L := 39 + i) (by omega), lg_eq hi]
    exact eqK_sound h1
  · obtain ⟨_, h2⟩ := (bAnd_iff _ _).1 (LC.all i hi)
    rw [lg_eq hi, a0_eq]
    exact commK_sound h2
  · obtain ⟨i, hi, rfl⟩ := prime_cases hp
    obtain ⟨h1, h2⟩ := (bAnd_iff _ _).1 (YO.all i hi)
    rw [y_eq hi]
    refine ⟨?_, neIdK_sound h2⟩
    rw [powEqRK_sound h1, idA_eq]
    exact eqA_self _
  · obtain ⟨i, hi, rfl⟩ := prime_cases hp
    obtain ⟨_, h2⟩ := (bAnd_iff _ _).1 (EC.all i hi)
    obtain ⟨h3, h4⟩ := (bAnd_iff _ _).1 h2
    obtain ⟨h5, h6⟩ := (bAnd_iff _ _).1 h4
    rw [v_eq hi]
    refine ⟨neIdK_sound h6, ?_⟩
    have hw : ∀ q < 8, powEqRK 4060 12 (mask 12) (4060 * 12) (WT (9 * i + q))
        (QT (14 * i + 13)) 32 (WT (9 * i + q + 1)) = true := by
      intro q hq
      have h := WC.all (8 * i + q) (by change 8 * i + q < 24; omega)
      unfold wok at h
      rw [strictB_eq', strictB_eq'] at h
      have e1 : Nat.div (8 * i + q) 8 = i := by
        change (8 * i + q) / 8 = i
        omega
      have e2 : Nat.mod (8 * i + q) 8 = q := by
        change (8 * i + q) % 8 = q
        omega
      rw [e1, e2] at h
      exact h
    have h0 : unpack 4060 12 (WT (9 * i + 0)) = idA 4060 := by
      rw [idA_eq, ← Nat.eq_of_beq_eq_true h3]
      all_goals rfl
    have := pow_chain (Q := fun q => WT (9 * i + q)) h0 hw 8 (Nat.le_refl 8)
    rw [show (256 : Nat) = 32 * 8 from rfl, this, idA_eq, ← Nat.eq_of_beq_eq_true h5]
    exact eqA_self _

end CertificateChecks.KernelSporSch.RuLW

end
