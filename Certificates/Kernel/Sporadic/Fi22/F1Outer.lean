
module

public import Certificates.Kernel.Sporadic.Fi22.F1OuterK
public import Certificates.Kernel.Sporadic.Fi22.E2067
public import CFSG.Certificates.Kernel.Misc.HexFlatSound
public import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CertificateChecks.KernelSpor.Fi22F1O

open CFSG.KC.Enum CFSG.KS CFSG.KS.Text CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.BfsPin CFSG.KS.SporSch
open CFSG.KC.Misc.ArrEnum CFSG.Monster.B.Fischer CFSG.Monster.B.Co2.Native
open CertificateChecks.KernelSpor

theorem perm3510 {L : Nat} (hL : L < 151) : permB 3510 12 (Fi22OutT.L L) = true := by
  have hs : ∀ s < 8, permSl s = true := by
    intro s hs
    interval_cases s
    exacts [permSl0, permSl1, permSl2, permSl3, permSl4, permSl5, permSl6, permSl7]
  have h := allN_spec (hs (L / 20) (by omega)) (L % 20) (Nat.mod_lt _ (by norm_num))
  rw [strictB_eq] at h
  have e : Nat.add (Nat.mul 20 (L / 20)) (L % 20) = L := by
    change 20 * (L / 20) + L % 20 = L
    omega
  rw [e] at h
  have hb : Nat.blt L 151 = true := Eq.mpr Nat.blt_eq hL
  rw [hb] at h
  exact h

theorem arr3510_eq {L : Nat} (hL : L < 151) : fi22OuterArr3510 L = unpack 3510 12 (Fi22OutT.L L) := by
  have h := hexBind_sound Fi22OutT.all L hL
  rw [Nat.zero_add, ← Fi22OutT.eq] at h
  exact h

theorem arr693_eq {L : Nat} (hL : L < 104) : fi22OuterArr693 L = unpack 693 10 (Fi22O693T.L L) := by
  have h := hexBind_sound Fi22O693T.all L hL
  rw [Nat.zero_add, ← Fi22O693T.eq] at h
  exact h

theorem arr256_eq {L : Nat} (hL : L < 16) : fi22OuterArr256 L = unpack 256 9 (Fi22O256T.L L) := by
  have h := hexBind_sound Fi22O256T.all L hL
  rw [Nat.zero_add, ← Fi22O256T.eq] at h
  exact h

theorem hex3_lt {s : String} {m B F : Nat} (h : hexTable3 m 0 s = unpack m 12 F)
    (hb : allN m (fun i => Nat.blt (pg 12 (mask 12) F i) B) = true) :
    ∀ x ∈ hex3List s m, x < B := by
  intro x hx
  simp only [hex3List, List.mem_map, List.mem_range] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  have e : (hexTable3 m 0 s)[k]! = CFSG.Monster.B.Max2.Native.hexAt s.toUTF8 (3 * k) 3 := by
    simp [hexTable3, hk]
  rw [← e, h, Orb.unpack_get hk]
  exact Eq.mp Nat.blt_eq (allN_spec hb k hk)

theorem mTab : hexTable3 693 0 fi22OuterMPointsHex = unpack 693 12 (Fi22OMP.F 0) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound Fi22OMP.all 0 (by norm_num)
  rw [← Fi22OMP.eq, Nat.mul_zero] at h
  exact h

theorem tTab : hexTable3 256 0 fi22OuterTPointsHex = unpack 256 12 (Fi22OTP.F 0) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound Fi22OTP.all 0 (by norm_num)
  rw [← Fi22OTP.eq, Nat.mul_zero] at h
  exact h

theorem wTab : hexTable3 693 0 fi22OuterWitnessOrbitsHex = unpack 693 12 (Fi22OWO.F 0) := by
  have h := CFSG.KC.Misc.HexFlat.hexTable3_sound Fi22OWO.all 0 (by norm_num)
  rw [← Fi22OWO.eq, Nat.mul_zero] at h
  exact h

theorem codesK_spec : ∀ {cs : List Char}, codesK cs = true → ∀ c ∈ cs, c.toNat < 52
  | [], _, c, hc => by cases hc
  | ch :: cs, h, c, hc => by
    obtain ⟨h1, h2⟩ := (bAnd_iff (Nat.blt (Char.toNat ch) 52) (codesK cs)).1 h
    rcases List.mem_cons.1 hc with rfl | hc
    · exact Eq.mp Nat.blt_eq h1
    · exact codesK_spec h2 c hc

theorem code_lt {cs : List Char} (h : codesK cs = true) {k : Nat} (hk : k < cs.length) :
    codeAt (String.ofList cs) k < 4 := by
  have hc := codesK_spec h
  have ha : ∀ c ∈ cs.take cs.length, c.toNat < 128 := fun c hc' => by
    rw [List.take_length] at hc'
    have := hc c hc'
    omega
  unfold codeAt
  rw [get!_toUTF8 ha hk hk]
  have h52 := hc _ (List.getElem_mem hk)
  have e : (UInt8.ofNat (cs[k]'hk).toNat).toNat = (cs[k]'hk).toNat := by
    rw [UInt8.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by omega)
  rw [e]
  omega

theorem facts3038 : layoutOK fi22Outer3510Bytes 3 3510 151 = true ∧
    layoutOK fi22Outer693Bytes 3 693 104 = true ∧
    layoutOK fi22Outer256Bytes 2 256 16 = true ∧
    (∀ L < 151, isInvA 3510 (fi22OuterArr3510 L) (invCand 3510 (fi22OuterArr3510 L)) = true) ∧
    (∀ L < 104, isInvA 693 (fi22OuterArr693 L) (invCand 693 (fi22OuterArr693 L)) = true) ∧
    (∀ L < 16, isInvA 256 (fi22OuterArr256 L) (invCand 256 (fi22OuterArr256 L)) = true) ∧
    (∀ x ∈ fi22OuterMPointsNat, x < 3510) ∧ (∀ x ∈ fi22OuterTPointsNat, x < 3510) ∧
    (∀ r < 3, ∀ x ∈ fi22OuterWitnessOrbitNat r, x < 693) ∧
    ((List.range 3).map fun r => (fi22OuterWitnessOrbitNat r).length) = [512, 180, 1] ∧
    fi22OuterUnitaryPoints.length = 693 * 6 ∧ fi22OuterTransvectionVectors.length = 46 * 6 ∧
    (∀ k < 693 * 6, codeAt fi22OuterUnitaryPoints k < 4) ∧
    (∀ k < 46 * 6, codeAt fi22OuterTransvectionVectors k < 4) ∧
    wordsOK fi22OuterMGenCount 17 fi22OuterMDerivations = true ∧
    wordsOK fi22OuterTGenCount 13 fi22OuterTDerivations = true ∧
    wordsOK fi22OuterT256GenCount 16 fi22OuterT256Derivations = true ∧
    wordsOK fi22OuterUnitaryGenCount 49 fi22OuterUnitaryDerivations = true ∧
    wordsOK fi22OuterM693GenCount 15 fi22OuterM693Derivations = true ∧
    wordsOK fi22OuterMComm693GenCount 14 fi22OuterMComm693Derivations = true ∧
    wordsOK fi22OuterD693GenCount 11 fi22OuterD693Derivations = true := by
  refine ⟨?_, ?_, ?_, fun L hL => Fi22E2067.isInv_of (arr3510_eq hL) (perm3510 hL),
    fun L hL => Fi22E2067.isInv_of (arr693_eq hL) (allN_spec perm693 L hL),
    fun L hL => Fi22E2067.isInv_of (arr256_eq hL) (allN_spec perm256 L hL),
    hex3_lt mTab mLt, hex3_lt tTab tLt, fun r _ x hx => ?_, ?_, ?_, ?_, fun k hk => ?_,
    fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fi22Outer3510Bytes, Fi22OutT.eq, Fi22E2067.layout_eq]
    exact hexBind_layout Fi22OutT.all rfl
  · rw [fi22Outer693Bytes, Fi22O693T.eq, Fi22E2067.layout_eq]
    exact hexBind_layout Fi22O693T.all rfl
  · rw [fi22Outer256Bytes, Fi22O256T.eq, Fi22E2067.layout_eq]
    exact hexBind_layout Fi22O256T.all rfl
  · simp only [fi22OuterWitnessOrbitNat] at hx
    exact hex3_lt wTab wLt x (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  · simp [fi22OuterWitnessOrbitNat, hex3List, fi22OuterWitnessOrbitSizes]
    decide
  · rw [Fi22OUP.eq, String.length_ofList]
    exact lenU
  · rw [Fi22OTV.eq, String.length_ofList]
    exact lenV
  · rw [Fi22OUP.eq]
    exact code_lt codesU (by rw [lenU]; exact hk)
  · rw [Fi22OTV.eq]
    exact code_lt codesV (by rw [lenV]; exact hk)
  all_goals rw [Fi22E2067.words_eq]
  · exact derivK_sound dM
  · exact derivK_sound dT
  · exact derivK_sound dT256
  · exact derivK_sound dU
  · exact derivK_sound dM693
  · exact derivK_sound dMC
  · exact derivK_sound dD

end CertificateChecks.KernelSpor.Fi22F1O

end
