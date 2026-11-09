module

public import Certificates.Kernel.SporSch.Pair.McLCheck
public import CFSG.Certificates.Kernel.SporSch.ChainSProof
public import CFSG.Certificates.Kernel.SporSch.ChainKCount
public import CFSG.Sporadic.SmallOddCore.GroupFacts
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.McLCentW

meta def strongM : Array (Array Nat) :=
  #[
    #[0, 55, 37, 178, 186, 206, 44, 216, 204, 165, 65, 15, 154, 232, 137, 162, 73, 171, 9, 172, 4,
      246, 102, 84, 176, 51, 260, 205, 161, 211, 127, 7, 108, 217, 149, 222, 115, 183, 66, 117,
      47, 124, 20, 238, 121, 111, 210, 92, 272, 153, 116, 128, 248, 28, 94, 147, 30, 133, 136, 32,
      56, 179, 31, 40, 69, 156, 93, 245, 236, 265, 239, 119, 271, 95, 196, 81, 41, 78, 214, 43,
      45, 99, 105, 72, 241, 80, 132, 212, 118, 14, 59, 97, 90, 139, 126, 207, 6, 255, 189, 160,
      268, 209, 177, 57, 184, 107, 131, 242, 63, 29, 157, 60, 263, 77, 163, 256, 258, 229, 98, 67,
      86, 129, 22, 191, 146, 158, 175, 85, 174, 10, 194, 143, 220, 168, 274, 226, 201, 141, 188,
      54, 251, 122, 259, 169, 148, 130, 53, 198, 123, 250, 36, 254, 140, 70, 68, 144, 96, 159,
      197, 155, 103, 182, 273, 24, 192, 266, 225, 109, 75, 106, 145, 237, 46, 152, 16, 38, 114,
      89, 134, 101, 244, 166, 76, 218, 164, 50, 62, 23, 142, 120, 17, 110, 125, 200, 203, 193, 48,
      224, 2, 79, 219, 253, 52, 181, 240, 235, 100, 25, 213, 87, 12, 199, 135, 208, 82, 34, 42,
      233, 1, 195, 88, 27, 247, 33, 104, 170, 61, 26, 264, 252, 267, 35, 230, 249, 223, 190, 19,
      221, 167, 71, 269, 150, 113, 64, 180, 49, 234, 202, 261, 21, 185, 138, 58, 39, 112, 243,
      187, 91, 215, 173, 270, 231, 83, 151, 228, 257, 11, 8, 3, 13, 227, 262, 74, 18, 5],
    #[264, 2, 1, 3, 231, 5, 6, 202, 164, 218, 10, 11, 233, 197, 59, 198, 123, 45, 18, 234, 115,
      256, 40, 167, 24, 159, 114, 30, 41, 68, 27, 84, 133, 241, 50, 266, 199, 97, 38, 39, 22, 28,
      142, 46, 105, 17, 43, 99, 48, 248, 34, 190, 273, 181, 54, 69, 209, 274, 58, 14, 98, 87, 140,
      63, 153, 77, 237, 173, 29, 55, 138, 222, 195, 221, 74, 103, 145, 65, 154, 109, 226, 268,
      148, 83, 31, 132, 192, 61, 139, 183, 90, 119, 127, 188, 235, 128, 225, 37, 60, 47, 146, 156,
      102, 75, 104, 44, 228, 172, 111, 79, 110, 108, 112, 157, 26, 20, 236, 217, 224, 91, 175,
      135, 147, 16, 214, 125, 152, 92, 95, 194, 162, 262, 85, 32, 182, 121, 246, 137, 70, 88, 62,
      212, 42, 208, 144, 76, 100, 122, 82, 210, 184, 151, 126, 64, 78, 215, 101, 113, 187, 25,
      168, 242, 130, 163, 8, 166, 165, 23, 160, 227, 203, 205, 107, 67, 174, 120, 271, 179, 178,
      177, 263, 53, 134, 89, 150, 191, 189, 158, 93, 186, 51, 185, 86, 272, 129, 72, 196, 13, 15,
      36, 260, 258, 7, 170, 204, 171, 206, 207, 143, 56, 149, 269, 141, 254, 124, 155, 220, 117,
      9, 219, 216, 73, 71, 265, 118, 96, 80, 169, 106, 250, 240, 4, 232, 12, 19, 94, 116, 66, 267,
      252, 230, 33, 161, 247, 244, 253, 136, 243, 49, 255, 229, 259, 239, 245, 213, 249, 21, 261,
      201, 251, 200, 257, 131, 180, 0, 223, 35, 238, 81, 211, 270, 176, 193, 52, 57],
    #[264, 1, 2, 5, 202, 3, 10, 231, 197, 198, 6, 18, 234, 164, 40, 218, 159, 30, 11, 233, 84,
      241, 59, 199, 24, 123, 114, 45, 28, 46, 17, 115, 99, 256, 34, 273, 167, 69, 54, 58, 14, 41,
      140, 68, 77, 27, 29, 133, 48, 222, 50, 221, 266, 145, 38, 97, 226, 268, 39, 22, 132, 61,
      142, 90, 119, 105, 235, 138, 43, 37, 173, 248, 195, 190, 74, 75, 181, 44, 172, 79, 209, 274,
      157, 83, 20, 98, 224, 87, 175, 147, 63, 153, 111, 152, 237, 95, 194, 55, 85, 32, 182, 121,
      137, 103, 125, 65, 228, 154, 127, 109, 144, 92, 112, 148, 26, 31, 210, 246, 192, 64, 139,
      101, 183, 25, 242, 104, 188, 108, 128, 225, 165, 262, 60, 47, 146, 156, 217, 102, 67, 120,
      42, 179, 62, 208, 110, 53, 134, 89, 113, 236, 158, 151, 93, 91, 107, 185, 135, 82, 150, 16,
      160, 214, 166, 163, 13, 130, 162, 36, 168, 227, 170, 171, 78, 70, 207, 88, 271, 212, 206,
      141, 263, 76, 100, 122, 187, 155, 220, 184, 126, 216, 73, 215, 118, 272, 96, 72, 196, 8, 9,
      23, 260, 250, 4, 203, 232, 205, 178, 174, 143, 80, 116, 267, 177, 254, 161, 191, 189, 136,
      15, 219, 186, 51, 49, 255, 86, 129, 56, 169, 106, 258, 230, 7, 204, 19, 12, 66, 149, 94,
      269, 253, 240, 21, 124, 261, 244, 252, 117, 257, 71, 265, 201, 251, 245, 239, 213, 223, 33,
      247, 229, 259, 200, 243, 131, 180, 0, 249, 52, 211, 57, 238, 270, 176, 193, 35, 81],
    #[83, 1, 2, 5, 29, 3, 222, 43, 250, 153, 248, 120, 19, 258, 21, 119, 25, 34, 88, 12, 118, 14,
      33, 23, 219, 16, 112, 50, 41, 4, 170, 86, 165, 22, 17, 246, 36, 225, 251, 175, 189, 28, 61,
      7, 181, 203, 226, 162, 48, 144, 27, 156, 217, 53, 259, 194, 184, 81, 139, 220, 103, 42, 87,
      235, 97, 145, 125, 186, 209, 91, 216, 110, 213, 121, 114, 85, 76, 77, 78, 204, 158, 57, 113,
      0, 192, 75, 31, 62, 18, 122, 237, 69, 178, 126, 104, 142, 218, 64, 230, 166, 100, 101, 102,
      60, 94, 105, 106, 107, 206, 232, 71, 207, 26, 82, 74, 224, 148, 261, 20, 15, 11, 73, 89,
      268, 266, 66, 93, 174, 140, 198, 133, 228, 240, 130, 134, 135, 247, 137, 256, 58, 128, 168,
      95, 260, 49, 65, 211, 188, 116, 157, 231, 151, 183, 9, 185, 155, 51, 149, 80, 274, 177, 273,
      47, 264, 229, 32, 99, 199, 141, 263, 30, 212, 215, 241, 127, 39, 176, 160, 92, 205, 254, 44,
      238, 152, 56, 154, 67, 202, 147, 40, 190, 191, 84, 193, 55, 227, 270, 201, 129, 167, 200,
      197, 187, 45, 79, 179, 108, 111, 208, 68, 236, 146, 171, 72, 243, 172, 70, 52, 96, 24, 59,
      221, 6, 253, 115, 37, 46, 195, 131, 164, 98, 150, 109, 233, 234, 63, 210, 90, 182, 245, 132,
      173, 257, 214, 244, 239, 35, 136, 10, 252, 8, 38, 249, 223, 180, 265, 138, 242, 13, 54, 143,
      117, 262, 169, 163, 255, 124, 267, 123, 269, 196, 271, 272, 161, 159],
    #[0, 1, 2, 5, 226, 3, 144, 209, 197, 69, 110, 58, 233, 164, 173, 97, 268, 17, 39, 234, 84,
      189, 138, 167, 24, 274, 26, 27, 28, 187, 30, 115, 133, 220, 170, 261, 199, 198, 38, 18, 70,
      41, 42, 150, 76, 45, 184, 99, 48, 71, 203, 135, 247, 65, 54, 218, 202, 159, 11, 67, 60, 128,
      62, 125, 194, 53, 94, 59, 158, 9, 40, 49, 180, 101, 112, 230, 44, 181, 215, 109, 231, 123,
      116, 163, 20, 85, 224, 95, 120, 152, 104, 225, 108, 147, 66, 87, 119, 15, 98, 47, 238, 73,
      137, 240, 90, 145, 131, 185, 92, 79, 10, 127, 74, 149, 114, 31, 82, 214, 192, 96, 88, 190,
      188, 81, 217, 63, 183, 111, 61, 153, 162, 106, 132, 32, 211, 51, 242, 102, 22, 175, 140,
      141, 142, 200, 6, 105, 267, 93, 236, 113, 43, 151, 89, 129, 155, 154, 221, 210, 68, 57, 171,
      246, 130, 83, 13, 166, 165, 23, 205, 254, 34, 160, 191, 14, 206, 139, 271, 177, 207, 179,
      72, 77, 269, 126, 46, 107, 256, 29, 122, 21, 121, 172, 118, 272, 64, 263, 196, 8, 37, 36,
      143, 250, 56, 50, 204, 168, 174, 178, 260, 7, 157, 134, 212, 227, 117, 78, 241, 124, 55,
      219, 33, 156, 248, 245, 86, 91, 4, 213, 262, 258, 75, 80, 232, 12, 19, 237, 148, 235, 100,
      249, 103, 216, 136, 273, 244, 223, 161, 52, 222, 239, 201, 259, 255, 265, 169, 252, 186,
      266, 229, 251, 208, 35, 228, 195, 264, 253, 257, 146, 16, 182, 270, 176, 193, 243, 25],
    #[0, 1, 2, 25, 187, 16, 41, 150, 240, 225, 28, 255, 144, 230, 177, 194, 209, 103, 265, 110,
      61, 182, 141, 4, 262, 226, 213, 75, 234, 274, 60, 87, 90, 146, 77, 261, 7, 175, 126, 82,
      160, 233, 241, 268, 17, 85, 159, 63, 200, 10, 105, 179, 247, 161, 93, 139, 127, 108, 113,
      168, 52, 101, 256, 239, 165, 27, 198, 33, 123, 39, 21, 6, 114, 212, 48, 191, 124, 34, 229,
      36, 111, 92, 130, 244, 42, 35, 220, 135, 125, 152, 245, 162, 184, 38, 218, 134, 148, 58,
      246, 237, 73, 216, 89, 155, 210, 50, 131, 201, 158, 23, 12, 56, 193, 166, 72, 62, 252, 215,
      189, 32, 104, 70, 188, 46, 8, 236, 54, 80, 100, 157, 69, 219, 217, 235, 51, 186, 185, 122,
      22, 94, 173, 142, 138, 112, 19, 273, 156, 183, 99, 253, 79, 106, 251, 47, 197, 44, 67, 133,
      204, 68, 269, 13, 64, 176, 98, 91, 97, 43, 267, 143, 107, 190, 164, 14, 3, 66, 163, 140,
      199, 95, 180, 266, 121, 147, 232, 181, 31, 109, 259, 118, 171, 65, 40, 169, 116, 74, 272,
      132, 37, 29, 195, 257, 202, 78, 57, 221, 167, 5, 26, 207, 249, 115, 128, 270, 258, 145, 20,
      154, 55, 151, 86, 205, 248, 88, 59, 149, 174, 260, 228, 243, 53, 231, 81, 71, 49, 129, 223,
      96, 84, 153, 76, 238, 250, 203, 271, 119, 172, 30, 222, 120, 242, 102, 15, 9, 196, 18, 211,
      170, 214, 137, 227, 45, 24, 254, 83, 11, 136, 224, 206, 192, 208, 264, 263, 117, 178]]

meta def baseM : Array Nat := #[1, 0, 3]

@[expose] def D : List (List Int) :=
  [[-2, 1, 1, 1, 1], [1, -2, 1, 2, -1, 2, -1], [-4, 3, 4], [1, 5, 1]]

end CertificateChecks.KernelSporSch.McLCentW

#ks_rawchain CertificateChecks.KernelSporSch.McLCentC 275 9 275
  CertificateChecks.KernelSporSch.McLCentW.strongM CertificateChecks.KernelSporSch.McLCentW.baseM 2
  CertificateChecks.KernelSporSch.McLCentW.D

namespace CertificateChecks.KernelSporSch.McLCent

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch CFSG.KS.SporSch.MOC
open CFSG.KS.SporSch.MBT CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu
open CertificateChecks.KernelSporSch

theorem chainS : ChainS 275 9 McLCentC.S McLCentC.SI McLCentC.LR McLCentC.TR McLCentC.TRI 6 2 3
    McLCentC.BP (strongArr 275 9 6 McLCentC.S) (baseArr 9 3 McLCentC.BP) McLCentW.D 1 275 :=
  ⟨⟨by norm_num, by norm_num, by norm_num, by simp [strongArr], fun j hj => by
      rw [strongArr, getElem!_pos _ j (by simpa using hj), Array.getElem_ofFn],
    by simp [baseArr], fun t ht => by
      rw [baseArr, getElem!_pos _ t (by simpa using ht), Array.getElem_ofFn]⟩,
    McLCentC.head, McLCentC.hl, by norm_num, .inl McLCentC.hs⟩

theorem base_nodup : (baseArr 9 3 McLCentC.BP).toList.Nodup := by decide +kernel

theorem mclChainS : ChainS 275 9 PMcL.S PMcL.SI PMcL.LR PMcL.TR PMcL.TRI 13 2 5 PMcL.BP
    mclStrongArrs PairMcL.baseArr PMcLWords.D 5 55 :=
  ⟨PMcLCheck.binds, PMcL.head, PMcL.hl, by norm_num, .inr PMcLCheck.hsP⟩

theorem mcl_base_nodup : CFSG.Sporadic.Schreier.PairMcL.baseArr.toList.Nodup := by decide

theorem ordH0 : Nat.beq (ordK McLCentC.LR 3) 40320 = true := by quickRfl

theorem ordK0 : Nat.beq (ordK PMcL.LR 5) 898128000 = true := by quickRfl

theorem c0 : canonK 275 9 (mask 9) (275 * 9) (McLCentC.S 0) = true := by quickRfl

theorem c1 : canonK 275 9 (mask 9) (275 * 9) (McLCentC.S 1) = true := by quickRfl

theorem s0 : siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) PMcL.LR PMcL.TRI PMcL.BP 5 0
    (McLCentC.S 0) = true := by quickRfl

theorem s1 : siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) PMcL.LR PMcL.TRI PMcL.BP 5 0
    (McLCentC.S 1) = true := by quickRfl

theorem m0 : Nat.beq (pcomp 275 9 (mask 9) (PMcL.S 0) (McLCentC.S 0))
    (pcomp 275 9 (mask 9) (McLCentC.S 0) (PMcL.S 0)) = true := by quickRfl

theorem m1 : Nat.beq (pcomp 275 9 (mask 9) (PMcL.S 0) (McLCentC.S 1))
    (pcomp 275 9 (mask 9) (McLCentC.S 1) (PMcL.S 0)) = true := by quickRfl

theorem ncard_le {gA gB : Equiv.Perm (Fin 275)}
    (hA : imageList gA = (unpack 275 9 (PMcL.S 0)).toList)
    (hB : imageList gB = (unpack 275 9 (PMcL.S 1)).toList) :
    (CFSG.Sporadic.SmallOddCore.conjClass (Subgroup.closure ({gA, gB} : Set (Equiv.Perm (Fin 275))))
      gA).ncard ≤ 22275 := by
  obtain ⟨h₁, p₁⟩ := perm_of_chainS chainS (j := 0) (by norm_num)
  obtain ⟨h₂, p₂⟩ := perm_of_chainS chainS (j := 1) (by norm_num)
  have hH : Nat.card (gen2 h₁ h₂) = 40320 := by
    rw [chainS_card_proved chainS p₁ p₂ base_nodup]
    exact Nat.eq_of_beq_eq_true ordH0
  have hK : Nat.card (gen2 gA gB) = 898128000 := by
    rw [chainS_card_proved mclChainS hA hB mcl_base_nodup]
    exact Nat.eq_of_beq_eq_true ordK0
  have hcomm : ∀ {h : Equiv.Perm (Fin 275)} {X : Nat}, imageList h = (unpack 275 9 X).toList →
      Nat.beq (pcomp 275 9 (mask 9) (PMcL.S 0) X) (pcomp 275 9 (mask 9) X (PMcL.S 0)) = true →
      h ∈ Subgroup.centralizer ({gA} : Set (Equiv.Perm (Fin 275))) := fun hX e => by
    have pA := prep_of_imageList hA
    have pX := prep_of_imageList hX
    rw [beq_pcomp_iff (by norm_num) (by norm_num) pA pX pX pA] at e
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (of_decide_eq_true e).symm
  have hle : gen2 h₁ h₂ ≤ gen2 gA gB ⊓ Subgroup.centralizer ({gA} : Set (Equiv.Perm (Fin 275))) := by
    rw [gen2, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨chainS_mem_proved mclChainS hA hB mcl_base_nodup p₁ c0 s0, hcomm p₁ m0⟩
    · exact ⟨chainS_mem_proved mclChainS hA hB mcl_base_nodup p₂ c1 s1, hcomm p₂ m1⟩
  have hfin : Finite (gen2 gA gB) := inferInstance
  have hc := CFSG.Sporadic.SmallOddCore.ncard_conjClass_mul_card (gen2 gA gB) gA
  have hl := Subgroup.card_le_of_le hle
  rw [hK] at hc
  rw [hH] at hl
  change (CFSG.Sporadic.SmallOddCore.conjClass (gen2 gA gB) gA).ncard ≤ 22275
  nlinarith

end CertificateChecks.KernelSporSch.McLCent

end
