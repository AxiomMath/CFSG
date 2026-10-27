module

public import Certificates.Data.Kernel.Misc.Sp6Transv
public import Certificates.Kernel.Sp62.Rec
public import Certificates.Kernel.SporSch.Th.GenV4
public import Certificates.Kernel.Co1B.GenTri2045
public meta import Certificates.Kernel.Misc.Sp6Transv.Gen

public section

set_option maxRecDepth 400000

#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.KS CFSG.KC.Misc.Sp6TransvGen.ksL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.TG CFSG.KC.Misc.Sp6TransvGen.tgL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.E CFSG.KC.Misc.Sp6TransvGen.eL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.P CFSG.KC.Misc.Sp6TransvGen.pL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.S CFSG.KC.Misc.Sp6TransvGen.sL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.C CFSG.KC.Misc.Sp6TransvGen.cL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.QG CFSG.KC.Misc.Sp6TransvGen.qgL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.EQ CFSG.KC.Misc.Sp6TransvGen.qeL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.QP CFSG.KC.Misc.Sp6TransvGen.qpL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.QS CFSG.KC.Misc.Sp6TransvGen.qsL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.QC CFSG.KC.Misc.Sp6TransvGen.qcL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.NB CFSG.KC.Misc.Sp6TransvGen.nbL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.K CFSG.KC.Misc.Sp6TransvGen.kL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.KP CFSG.KC.Misc.Sp6TransvGen.kpL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.KI CFSG.KC.Misc.Sp6TransvGen.kiL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.SQ CFSG.KC.Misc.Sp6TransvGen.sqL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.SKI CFSG.KC.Misc.Sp6TransvGen.skL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.SE CFSG.KC.Misc.Sp6TransvGen.seL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.SPP CFSG.KC.Misc.Sp6TransvGen.sppL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.SS CFSG.KC.Misc.Sp6TransvGen.ssL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.EZ CFSG.KC.Misc.Sp6TransvGen.ezL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.PZ CFSG.KC.Misc.Sp6TransvGen.pzL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.SZ CFSG.KC.Misc.Sp6TransvGen.szL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.CZ CFSG.KC.Misc.Sp6TransvGen.czL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.TW CFSG.KC.Misc.Sp6TransvGen.twL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.OE CFSG.KC.Misc.Sp6TransvGen.oeL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.OP CFSG.KC.Misc.Sp6TransvGen.opL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.OS CFSG.KC.Misc.Sp6TransvGen.osL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.L CFSG.KC.Misc.Sp6TransvGen.lcL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.LI CFSG.KC.Misc.Sp6TransvGen.liL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.REP CFSG.KC.Misc.Sp6TransvGen.repL
#kss_natlist CertificateChecks.KernelMisc.Sp6Transv.WR CFSG.KC.Misc.Sp6TransvGen.wrL

namespace CertificateChecks.KernelMisc.Sp6Transv

open CFSG.KC.Ord CFSG.KC.Misc.Clos CFSG.KC.Misc.Sp6Transv CFSG.KD.Sp62
open CFSG.KC.LQT.P (letB allN allL)

@[expose] noncomputable def trB (h : Nat) : Bool :=
  allR (Nat.mul 256 h) 256 (treeAt MULF ONE TG 4 E P)

@[expose] noncomputable def srB (_ : Nat) : Bool := allR 0 512 (sortAt 512 E S)

@[expose] noncomputable def clB (h : Nat) : Bool :=
  allR (Nat.mul 256 h) 256 (closedAt MULF TG 4 512 E C)

@[expose] noncomputable def twB (_ : Nat) : Bool :=
  allN 4 fun l => Nat.beq (TG l)
    (wordF (fun i => KS (Nat.add 5 (Nat.mod i 4))) (Nat.mod (TW l) 16) (Nat.div (TW l) 16))

@[expose] noncomputable def qB (_ : Nat) : Bool :=
  andB (allR 0 32 (treeAt MULF ONE QG 5 EQ QP))
    (andB (allR 0 32 (sortAt 32 EQ QS)) (andB (allR 0 32 (closedAt MULF QG 5 32 EQ QC))
      (andB (abelQ EQ) (andB (countQ EQ (KS 1) (KS 3))
        (andB (allR 0 9 (treeAt MULF ONE (fun l => KS (Nat.add 1 (Nat.mul 2 l))) 2 EZ PZ))
          (andB (allR 0 9 (sortAt 9 EZ SZ))
            (allR 0 9 (closedAt MULF (fun l => KS (Nat.add 1 (Nat.mul 2 l))) 2 9 EZ CZ))))))))

@[expose] noncomputable def inB (h : Nat) : Bool :=
  allR (Nat.mul 256 h) 256
    (interAt E S EQ NB (MULF (KS 5) (KS 5)) (MULF (KS 7) (KS 7)))

@[expose] noncomputable def spB (_ : Nat) : Bool :=
  andB (allR 0 12 (treeAt MULF ONE (fun l => KS (Nat.add 5 l)) 2 K KP))
    (andB (allR 0 12 (invAt K KI))
      (andB (allR 0 30 (spanAt EQ SQ SKI K KI SE SPP SS)) (coverQ EQ SQ (KS 0))))

@[expose] noncomputable def obB (_ : Nat) : Bool :=
  andB (allR 0 63 (treeAt (fun x l => conjF (KS (Nat.add 9 l)) (KS (Nat.add 11 l)) x) (KS 0)
      (fun l => l) 2 OE OP))
    (allR 0 63 (sortAt 63 OE OS))

@[expose] noncomputable def wB (_ : Nat) : Bool :=
  andB (allR 0 81 (wordAt (KS 1) (KS 2) (KS 3) (KS 4) L LI REP WR))
    (allL [27, 54, 9, 18, 3, 6] fun w => Nat.beq (Nat.mod (WR w) 4) 1)

@[expose] noncomputable def fB (h : Nat) : Bool :=
  letB (MULF (KS 2) (KS 2)) fun z1s =>
    allR (Nat.mul 540 h) 540
      (filtAt REC (KS 0) (KS 2) z1s (KS 3) (MULF (MULF (KS 2) (KS 0)) z1s)
        (MULF (MULF z1s (KS 0)) (KS 2)))

end CertificateChecks.KernelMisc.Sp6Transv

#kc_slices CertificateChecks.KernelMisc.Sp6Transv.TK CertificateChecks.KernelMisc.Sp6Transv.trB 2
#kc_slices CertificateChecks.KernelMisc.Sp6Transv.SK CertificateChecks.KernelMisc.Sp6Transv.srB 1
#kc_slices CertificateChecks.KernelMisc.Sp6Transv.CK CertificateChecks.KernelMisc.Sp6Transv.clB 2
#kc_slices CertificateChecks.KernelMisc.Sp6Transv.GK CertificateChecks.KernelMisc.Sp6Transv.twB 1
#kc_slices CertificateChecks.KernelMisc.Sp6Transv.QK CertificateChecks.KernelMisc.Sp6Transv.qB 1
#kc_slices CertificateChecks.KernelMisc.Sp6Transv.IK CertificateChecks.KernelMisc.Sp6Transv.inB 2
#kc_slices CertificateChecks.KernelMisc.Sp6Transv.PK CertificateChecks.KernelMisc.Sp6Transv.spB 1
#kc_slices CertificateChecks.KernelMisc.Sp6Transv.OK CertificateChecks.KernelMisc.Sp6Transv.obB 1
#kc_slices CertificateChecks.KernelMisc.Sp6Transv.WK CertificateChecks.KernelMisc.Sp6Transv.wB 1
#kc_slices CertificateChecks.KernelMisc.Sp6Transv.FK CertificateChecks.KernelMisc.Sp6Transv.fB 4

end
