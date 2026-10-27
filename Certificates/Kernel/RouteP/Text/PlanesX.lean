module

public import CFSG.Certificates.Kernel.RouteP.TextLines
public import Certificates.Kernel.RouteP.Text.Data
public import Certificates.Data.RouteP.Q0Planes
public meta import CFSG.Certificates.Kernel.Common.StrChunks
public import CFSG.Certificates.Kernel.Common.StrChunks

public section

set_option maxRecDepth 1000000

#str_chunks CertificateChecks.KernelRouteP.PX
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native.planesXText 140000 1000000 512
#str_chunks CertificateChecks.KernelRouteP.PG
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native.planeGensText 140000 1000000 512

namespace CertificateChecks.KernelRouteP

open CFSG.KC.RouteP CFSG.KD.RouteP CFSG.KS.RouteP
  CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

@[expose] noncomputable def pgLens (i : Nat) : Nat :=
  nIf(Nat.blt i (nat_lit 16), nat_lit 891, nat_lit 21)

theorem pgLens_eq (i : Nat) : pgLens i = if i < 16 then 891 else 21 := by
  unfold pgLens
  by_cases h : i < 16
  · rw [if_pos h, (Nat.blt_eq.mpr h : Nat.blt i 16 = true)]
  · rw [if_neg h, (Bool.eq_false_iff.mpr fun e => h (Nat.blt_eq.mp e) : Nat.blt i 16 = false)]

set_option maxHeartbeats 0 in
theorem px_chk : nlChk PXE (fun _ => 24) (PX.chars.map Char.toNat) 0 0 0 0 0 1 (nlEnd 891) =
    true := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem pg_chk : nlChk PGE pgLens (PG.chars.map Char.toNat) 0 0 0 0 0 1 (nlEnd 17) = true := by
  decide +kernel

theorem rec32_lt (T : Nat → Nat) (r : Nat) : rec32 T r < 2 ^ 32 := by
  unfold rec32
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem toNat_ofNat_rec32 (T : Nat → Nat) (r : Nat) :
    (UInt32.ofNat (rec32 T r)).toNat = rec32 T r := by
  rw [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (rec32_lt T r)]

theorem planeXData_get : (planeXData ()).size = 891 ∧ ∀ i < 891, ((planeXData ())[i]!).size = 24 ∧
    ∀ j < 24, ((planeXData ())[i]!)[j]! = PXE i j := by
  obtain ⟨h1, h2⟩ := numLines_of_chk PXE (fun _ => 24) px_chk
  unfold planeXData
  rw [PX.eq]
  refine ⟨by rw [Array.size_map, h1], fun i hi => ?_⟩
  obtain ⟨h3, h4⟩ := h2 i hi
  have e : ((numLines (String.ofList PX.chars)).map fun l => l.map UInt32.toNat)[i]! =
      ((numLines (String.ofList PX.chars))[i]!).map UInt32.toNat := by
    rw [getElem!_pos _ _ (by rw [Array.size_map, h1]; exact hi), Array.getElem_map,
      getElem!_pos _ _ (by rw [h1]; exact hi)]
  rw [e]
  refine ⟨by rw [Array.size_map, h3], fun j hj => ?_⟩
  rw [getElem!_pos _ _ (by rw [Array.size_map, h3]; exact hj), Array.getElem_map,
    ← getElem!_pos _ _ (by rw [h3]; exact hj), h4 j hj]
  exact toNat_ofNat_rec32 _ _

theorem planeGenData_get : (planeGenData ()).size = 17 ∧ ∀ i < 17,
    ((planeGenData ())[i]!).size = pgLens i ∧
      ∀ j < pgLens i, ((planeGenData ())[i]!)[j]! = PGE i j := by
  obtain ⟨h1, h2⟩ := numLines_of_chk PGE pgLens pg_chk
  unfold planeGenData
  rw [PG.eq]
  refine ⟨by rw [Array.size_map, h1], fun i hi => ?_⟩
  obtain ⟨h3, h4⟩ := h2 i hi
  have e : ((numLines (String.ofList PG.chars)).map fun l => l.map UInt32.toNat)[i]! =
      ((numLines (String.ofList PG.chars))[i]!).map UInt32.toNat := by
    rw [getElem!_pos _ _ (by rw [Array.size_map, h1]; exact hi), Array.getElem_map,
      getElem!_pos _ _ (by rw [h1]; exact hi)]
  rw [e]
  refine ⟨by rw [Array.size_map, h3], fun j hj => ?_⟩
  rw [getElem!_pos _ _ (by rw [Array.size_map, h3]; exact hj), Array.getElem_map,
    ← getElem!_pos _ _ (by rw [h3]; exact hj), h4 j hj]
  exact toNat_ofNat_rec32 _ _

end CertificateChecks.KernelRouteP
