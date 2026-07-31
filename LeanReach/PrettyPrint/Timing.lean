namespace LeanReach

structure PPTiming where
  importNanos : Nat := 0
  privateOverlayNanos : Nat := 0
  preparationNanos : Nat := 0
  signatureNanos : Nat := 0
  bodyNanos : Nat := 0
  sidecarWriteNanos : Nat := 0

instance : Add PPTiming where
  add left right := {
    importNanos := left.importNanos + right.importNanos
    privateOverlayNanos := left.privateOverlayNanos + right.privateOverlayNanos
    preparationNanos := left.preparationNanos + right.preparationNanos
    signatureNanos := left.signatureNanos + right.signatureNanos
    bodyNanos := left.bodyNanos + right.bodyNanos
    sidecarWriteNanos := left.sidecarWriteNanos + right.sidecarWriteNanos
  }

def PPTiming.profile (timing : PPTiming) : String :=
  let ms nanos := nanos / 1000000
  s!"import={ms timing.importNanos}ms \
    private-overlay={ms timing.privateOverlayNanos}ms \
    prepare={ms timing.preparationNanos}ms \
    signature-pp={ms timing.signatureNanos}ms \
    body-pp={ms timing.bodyNanos}ms \
    sidecar-write={ms timing.sidecarWriteNanos}ms"

end LeanReach
