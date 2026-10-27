module

public import Certificates.Data.Kernel.J2H2.Echelon
public import Certificates.Kernel.J2H2.Data
public import Certificates.Data.J2H2Sylow
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CFSG.KD.J2H2

open CFSG.KC.Enum CFSG.ComponentClassification.J2Cover.Models CFSG.RankThree.PartTwo.J2Residue

theorem mask0 : maskBlk YC MTP LMP GP PP CKB MB 0 = true := by quickRfl
theorem mask1 : maskBlk YC MTP LMP GP PP CKB MB 1 = true := by quickRfl
theorem mask2 : maskBlk YC MTP LMP GP PP CKB MB 2 = true := by quickRfl
theorem mask3 : maskBlk YC MTP LMP GP PP CKB MB 3 = true := by quickRfl
theorem mask4 : maskBlk YC MTP LMP GP PP CKB MB 4 = true := by quickRfl
theorem mask5 : maskBlk YC MTP LMP GP PP CKB MB 5 = true := by quickRfl
theorem mask6 : maskBlk YC MTP LMP GP PP CKB MB 6 = true := by quickRfl
theorem mask7 : maskBlk YC MTP LMP GP PP CKB MB 7 = true := by quickRfl
theorem mask8 : maskBlk YC MTP LMP GP PP CKB MB 8 = true := by quickRfl
theorem mask9 : maskBlk YC MTP LMP GP PP CKB MB 9 = true := by quickRfl
theorem mask10 : maskBlk YC MTP LMP GP PP CKB MB 10 = true := by quickRfl
theorem mask11 : maskBlk YC MTP LMP GP PP CKB MB 11 = true := by quickRfl
theorem mask12 : maskBlk YC MTP LMP GP PP CKB MB 12 = true := by quickRfl
theorem mask13 : maskBlk YC MTP LMP GP PP CKB MB 13 = true := by quickRfl
theorem mask14 : maskBlk YC MTP LMP GP PP CKB MB 14 = true := by quickRfl
theorem mask15 : maskBlk YC MTP LMP GP PP CKB MB 15 = true := by quickRfl

theorem ech0 : echChunk MB ST KS 0 = true := by quickRfl
theorem ech1 : echChunk MB ST KS 1 = true := by quickRfl
theorem ech2 : echChunk MB ST KS 2 = true := by quickRfl
theorem ech3 : echChunk MB ST KS 3 = true := by quickRfl
theorem ech4 : echChunk MB ST KS 4 = true := by quickRfl
theorem ech5 : echChunk MB ST KS 5 = true := by quickRfl

theorem ksOK : ksK GP PP H2S.h2Free KS ST YC C4725.aCols C4725.bCols yWords = true := by quickRfl

theorem depthOK : depthK PP = true := by quickRfl

end CFSG.KD.J2H2

end
