namespace LeanReach

structure PPTiming where
  importNanos : Nat := 0
  privateOverlayNanos : Nat := 0
  signatureNanos : Nat := 0
  bodyNanos : Nat := 0
  sidecarWriteNanos : Nat := 0

def PPTiming.add (left right : PPTiming) : PPTiming where
  importNanos := left.importNanos + right.importNanos
  privateOverlayNanos := left.privateOverlayNanos + right.privateOverlayNanos
  signatureNanos := left.signatureNanos + right.signatureNanos
  bodyNanos := left.bodyNanos + right.bodyNanos
  sidecarWriteNanos := left.sidecarWriteNanos + right.sidecarWriteNanos

instance : Add PPTiming := ⟨PPTiming.add⟩

def PPTiming.profile (timing : PPTiming) : String :=
  let ms nanos := nanos / 1000000
  s!"import={ms timing.importNanos}ms \
    private-overlay={ms timing.privateOverlayNanos}ms \
    signature-pp={ms timing.signatureNanos}ms \
    body-pp={ms timing.bodyNanos}ms \
    sidecar-write={ms timing.sidecarWriteNanos}ms"

end LeanReach
