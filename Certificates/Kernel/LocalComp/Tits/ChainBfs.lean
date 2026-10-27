module

public import Certificates.Kernel.LocalComp.Tits.ChainData
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelLC.Tits

open CFSG.KC.LocalComp.TitsChain

theorem kBfs0 : bfsOK TL TTf TSf szf CP 0 = true := by quickRfl

theorem kBfs1 : bfsOK TL TTf TSf szf CP 1 = true := by quickRfl

theorem kBfs2 : bfsOK TL TTf TSf szf CP 2 = true := by quickRfl

theorem kBfs3 : bfsOK TL TTf TSf szf CP 3 = true := by quickRfl

theorem kDepth0 : depthOK TTf szf 0 = true := by quickRfl

theorem kDepth1 : depthOK TTf szf 1 = true := by quickRfl

theorem kDepth2 : depthOK TTf szf 2 = true := by quickRfl

theorem kDepth3 : depthOK TTf szf 3 = true := by quickRfl

theorem kBfs : ∀ i < 4, bfsOK TL TTf TSf szf CP i = true := fun i hi => by
  match i, hi with
  | 0, _ => exact kBfs0
  | 1, _ => exact kBfs1
  | 2, _ => exact kBfs2
  | 3, _ => exact kBfs3

theorem kDepth : ∀ i < 4, depthOK TTf szf i = true := fun i hi => by
  match i, hi with
  | 0, _ => exact kDepth0
  | 1, _ => exact kDepth1
  | 2, _ => exact kDepth2
  | 3, _ => exact kDepth3

end CertificateChecks.KernelLC.Tits
