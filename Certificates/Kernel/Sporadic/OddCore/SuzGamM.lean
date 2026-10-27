module

public import Certificates.Kernel.Sporadic.OddCore.SuzGamS
public import Certificates.Kernel.Sporadic.OddCore.SuzCert
public import Certificates.Kernel.Sporadic.OddCore.SuzLocal
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSpor.OddCore.SGam

open CFSG.KC.Enum CFSG.KC.G2294 CertificateChecks.KernelSpor

@[expose] noncomputable def hashAll (i : Nat) : Bool :=
  hashL (Nat.div i (nat_lit 23)) (Nat.mod i (nat_lit 23))

@[expose] noncomputable def baseAll (i : Nat) : Bool :=
  baseL (Nat.div i (nat_lit 23)) (Nat.mod i (nat_lit 23))

@[expose] noncomputable def initL (s : Nat) : Bool :=
  strictB (SuzGamC (nat_lit 1)) fun C => blkL (initOK C) s

@[expose] noncomputable def oneL (s : Nat) : Bool :=
  strictB (SuzGamC (nat_lit 0)) fun C => blkL (fun v => Nat.beq (cs C v) (nat_lit 1)) s

@[expose] noncomputable def treeL (s : Nat) : Bool :=
  blkL (treeOK (nat_lit 22880) (nat_lit 2) SuzGamG SuzGamT) s

@[expose] noncomputable def genL (k s : Nat) : Bool :=
  strictB (SuzGamG k) fun G => blkL (fun x => Nat.beq (gp G x)
    (CFSG.KS.Row.rg (nat_lit 15) (CFSG.KS.mask (nat_lit 15)) SuzCertT.F (Nat.mul (nat_lit 715) k) x)) s

@[expose] noncomputable def genAll (i : Nat) : Bool :=
  genL (Nat.div i (nat_lit 23)) (Nat.mod i (nat_lit 23))

end CertificateChecks.KernelSpor.OddCore.SGam

#kss_each CertificateChecks.KernelSpor.OddCore.SGam.Hash CertificateChecks.KernelSpor.OddCore.SGam.hashAll 161
#kss_each CertificateChecks.KernelSpor.OddCore.SGam.Base CertificateChecks.KernelSpor.OddCore.SGam.baseAll 92
#kss_each CertificateChecks.KernelSpor.OddCore.SGam.Init CertificateChecks.KernelSpor.OddCore.SGam.initL 23
#kss_each CertificateChecks.KernelSpor.OddCore.SGam.One CertificateChecks.KernelSpor.OddCore.SGam.oneL 23
#kss_each CertificateChecks.KernelSpor.OddCore.SGam.Tree CertificateChecks.KernelSpor.OddCore.SGam.treeL 23
#kss_each CertificateChecks.KernelSpor.OddCore.SGam.Gen CertificateChecks.KernelSpor.OddCore.SGam.genAll 46

namespace CertificateChecks.KernelSpor.OddCore.SGam

open CFSG.KC.Enum CFSG.KC.G2294 CertificateChecks.KernelSpor

theorem sym0 : allN 280 (sym0OK SuzGamR) = true := by quickRfl

theorem root : allN 280 (fun i => Nat.beq (CFSG.KC.N3153.rg (SuzGamR 0) i)
    (pg 15 (CFSG.KS.mask 15) (SuzLocT.F 0) i)) = true := by quickRfl

theorem movers : bAnd(Nat.beq (gp (SuzGamG 0) 1) 0, bAnd(Nat.beq (gp (SuzGamG 1) (gp (SuzGamG 1) 2)) 0,
    Nat.beq (gp (SuzGamG 0) (gp (SuzGamG 1) (gp (SuzGamG 1) 3))) 0)) = true := by quickRfl

theorem cell1 : strictB (SuzGamC 4) (fun C => Nat.ble (cellCnt 22880 C (cs C 1)) 8505) = true := by
  quickRfl

theorem cell2 : strictB (SuzGamC 7) (fun C => Nat.ble (cellCnt 22880 C (cs C 2)) 1152) = true := by
  quickRfl

theorem cell3 : strictB (SuzGamC 9) (fun C => Nat.ble (cellCnt 22880 C (cs C 3)) 4) = true := by
  quickRfl

theorem inj : strictB (SuzGamC 12) (fun C => strictB (SuzGamO 0) fun P => injK 22880 C P) = true := by
  quickRfl

end CertificateChecks.KernelSpor.OddCore.SGam

end
