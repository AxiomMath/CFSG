module

public import Certificates.Kernel.MonsterB.Conj3054Data
public import CFSG.Certificates.Kernel.SortTreeSlice
import CFSG.Certificates.Kernel.Common.Harness
public import Std.Data.HashMap

public section

namespace CertificateChecks.Conj3054

open CFSG.KC.SortTree CFSG.KLie.CT

set_option maxRecDepth 100000

theorem t0 : treeSl actC 24 (fun _ => true) rootK recC 56925 484 4 16 64 0 64 = true := by quickRfl
theorem t1 : treeSl actC 24 (fun _ => true) rootK recC 56925 484 4 16 64 64 64 = true := by
  quickRfl
theorem t2 : treeSl actC 24 (fun _ => true) rootK recC 56925 484 4 16 64 128 64 = true := by
  quickRfl
theorem t3 : treeSl actC 24 (fun _ => true) rootK recC 56925 484 4 16 64 192 64 = true := by
  quickRfl
theorem t4 : treeSl actC 24 (fun _ => true) rootK recC 56925 484 4 16 64 256 64 = true := by
  quickRfl
theorem t5 : treeSl actC 24 (fun _ => true) rootK recC 56925 484 4 16 64 320 64 = true := by
  quickRfl
theorem t6 : treeSl actC 24 (fun _ => true) rootK recC 56925 484 4 16 64 384 64 = true := by
  quickRfl
theorem t7 : treeSl actC 24 (fun _ => true) rootK recC 56925 484 4 16 64 448 64 = true := by
  quickRfl
theorem t8 : treeSl actC 24 (fun _ => true) rootK recC 56925 484 4 16 64 512 64 = true := by
  quickRfl
theorem t9 : treeSl actC 24 (fun _ => true) rootK recC 56925 484 4 16 64 576 64 = true := by
  quickRfl
theorem t10 : treeSl actC 24 (fun _ => true) rootK recC 56925 484 4 16 64 640 64 = true := by
  quickRfl
theorem t11 : treeSl actC 24 (fun _ => true) rootK recC 56925 484 4 16 64 704 64 = true := by
  quickRfl
theorem t12 : treeSl actC 24 (fun _ => true) rootK recC 56925 484 4 16 64 768 64 = true := by
  quickRfl
theorem t13 : treeSl actC 24 (fun _ => true) rootK recC 56925 484 4 16 64 832 64 = true := by
  quickRfl

end CertificateChecks.Conj3054

end
