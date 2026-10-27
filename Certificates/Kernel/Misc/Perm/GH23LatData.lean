module

public import Certificates.Data.Kernel.Misc.PermGH23Lat
public import Certificates.Kernel.Misc.Perm.GH23K
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_ktree CertificateChecks.KernelMisc.GH23Lat RO
  "Certificates/Kernel/Misc/Perm/GH23Lat/data/ro.bin" 2 4 82 11677696143191671653
#kc_repo #kc_ktree CertificateChecks.KernelMisc.GH23Lat RP
  "Certificates/Kernel/Misc/Perm/GH23Lat/data/rep.bin" 24 4 49368 9680913584436014962
#kc_repo #kc_ktree CertificateChecks.KernelMisc.GH23Lat WX
  "Certificates/Kernel/Misc/Perm/GH23Lat/data/word.bin" 24 4 394944 6438252867976173105

namespace CertificateChecks.KernelMisc.GH23Lat

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.Misc.GH23 CertificateChecks.KernelMisc.GH23

@[expose] noncomputable def nR (m : Nat) : Nat := Nat.sub (RO (Nat.succ m)) (RO m)

@[expose] noncomputable def rcd (m j : Nat) : Nat := RP (Nat.add (RO m) j)

@[expose] noncomputable def RA (m j : Nat) : Nat := fld (rcd m j) (nat_lit 0) (nat_lit 15)

@[expose] noncomputable def covS (W : Nat → Nat) (m0 s : Nat) : Bool :=
  letB (Nat.div s (nat_lit 10)) fun d => letB (Nat.add m0 d) fun m =>
    allR (Nat.mul (nat_lit 2016) (Nat.mod s (nat_lit 10))) (nat_lit 2016)
      (covAt (eM m) (eM (nat_lit 40)) (RA m)
        (fun k => lane W (nat_lit 64) (nat_lit 8) (Nat.add (Nat.mul (nat_lit 20160) d) k))
        (NN m) (nR m))

@[expose] noncomputable def joinJ (m j : Nat) : Bool :=
  joinAt (eM m) (NN m) (gM m) (NG m) (eM (nat_lit 40)) (NN (nat_lit 40)) eM NN NG gM (rcd m j)
    (fun i => WX (Nat.add (Nat.mul (nat_lit 8) (Nat.add (RO m) j)) i))

@[expose] noncomputable def joinS (m : Nat) : Bool := allN (nR m) (joinJ m)

end CertificateChecks.KernelMisc.GH23Lat

end
