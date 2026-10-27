module

public import Certificates.Kernel.SporSch.PairJ3.CntFns
public meta import Certificates.Kernel.Misc.Perm.HexCmd
public meta import Certificates.Kernel.Misc.Perm.Cmd
public import CFSG.Certificates.Kernel.SporSch.PairClTSound
public import CFSG.Certificates.Kernel.SporSch.PairKSound
public import Certificates.Kernel.Misc.Perm.Cmd
public import Certificates.Kernel.Misc.Perm.HexCmd

namespace CertificateChecks.KernelSporSch.C81In

meta def hexT : String := include_str "../../../../CFSG/Sporadic/SmallOddCore/J3Cent.txt"

meta def hv (c : UInt8) : Nat :=
  if c.toNat < 58 then c.toNat - 48 else if c.toNat < 71 then c.toNat - 55 else c.toNat - 87

meta def tabs : Array (Array Nat) :=
  let b := hexT.toUTF8
  Array.ofFn (n := 31) fun k => Array.ofFn (n := 6156) fun i =>
    (List.range 4).foldl (fun a t => a * 16 + hv (b.get! (4 * (6156 * k.val + i.val) + t))) 0

meta def tabsI : Array (Array Nat) :=
  tabs.map fun p => Id.run do
    let mut r := Array.replicate 6156 0
    for i in [0:6156] do
      r := r.set! p[i]! i
    return r

meta def sN : String := include_str "c81/s_nf.hex"
meta def sB : String := include_str "c81/s_bit.hex"
meta def sP : String := include_str "c81/s_par.hex"
meta def sG : String := include_str "c81/s_gen.hex"
meta def sM : String := include_str "c81/s_mul.hex"
meta def sO : String := include_str "c81/s_ord.hex"
meta def sW : String := include_str "c81/s_wf.hex"
meta def sX : String := include_str "c81/s_wit.hex"
meta def o1P : String := include_str "c81/o1_pt.hex"
meta def o1R : String := include_str "c81/o1_par.hex"
meta def o1G : String := include_str "c81/o1_gen.hex"
meta def o1Q : String := include_str "c81/o1_pos.hex"
meta def o2P : String := include_str "c81/o2_pt.hex"
meta def o2R : String := include_str "c81/o2_par.hex"
meta def o2G : String := include_str "c81/o2_gen.hex"
meta def o2Q : String := include_str "c81/o2_pos.hex"
meta def cL : String := include_str "c81/cls.hex"
meta def cK : String := include_str "c81/clsk.hex"

end CertificateChecks.KernelSporSch.C81In

#kmisc_packarrs CertificateChecks.KernelSporSch.C81T.P CertificateChecks.KernelSporSch.C81In.tabs 13
#kmisc_packarrs CertificateChecks.KernelSporSch.C81T.I CertificateChecks.KernelSporSch.C81In.tabsI 13

#kmisc_tree CertificateChecks.KernelSporSch.C81D.SN CertificateChecks.KernelSporSch.C81In.sN 16 256
#kmisc_tree CertificateChecks.KernelSporSch.C81D.SB CertificateChecks.KernelSporSch.C81In.sB 1 256
#kmisc_tree CertificateChecks.KernelSporSch.C81D.SP CertificateChecks.KernelSporSch.C81In.sP 2 256
#kmisc_tree CertificateChecks.KernelSporSch.C81D.SG CertificateChecks.KernelSporSch.C81In.sG 1 256
#kmisc_tree CertificateChecks.KernelSporSch.C81D.SM CertificateChecks.KernelSporSch.C81In.sM 2 2048
#kmisc_tree CertificateChecks.KernelSporSch.C81D.SO CertificateChecks.KernelSporSch.C81In.sO 2 256
#kmisc_tree CertificateChecks.KernelSporSch.C81D.SW CertificateChecks.KernelSporSch.C81In.sW 1 256
#kmisc_tree CertificateChecks.KernelSporSch.C81D.SX CertificateChecks.KernelSporSch.C81In.sX 16 256
#kmisc_tree CertificateChecks.KernelSporSch.C81D.O1P CertificateChecks.KernelSporSch.C81In.o1P 4 960
#kmisc_tree CertificateChecks.KernelSporSch.C81D.O1R CertificateChecks.KernelSporSch.C81In.o1R 4 960
#kmisc_tree CertificateChecks.KernelSporSch.C81D.O1G CertificateChecks.KernelSporSch.C81In.o1G 1 960
#kmisc_tree CertificateChecks.KernelSporSch.C81D.O1Q CertificateChecks.KernelSporSch.C81In.o1Q 4 6156
#kmisc_tree CertificateChecks.KernelSporSch.C81D.O2P CertificateChecks.KernelSporSch.C81In.o2P 4 1224
#kmisc_tree CertificateChecks.KernelSporSch.C81D.O2R CertificateChecks.KernelSporSch.C81In.o2R 4 1224
#kmisc_tree CertificateChecks.KernelSporSch.C81D.O2G CertificateChecks.KernelSporSch.C81In.o2G 1 1224
#kmisc_tree CertificateChecks.KernelSporSch.C81D.O2Q CertificateChecks.KernelSporSch.C81In.o2Q 4 6156
#kmisc_tree CertificateChecks.KernelSporSch.C81D.CL CertificateChecks.KernelSporSch.C81In.cL 16 20520
#kmisc_tree CertificateChecks.KernelSporSch.C81D.CK CertificateChecks.KernelSporSch.C81In.cK 13 20520
