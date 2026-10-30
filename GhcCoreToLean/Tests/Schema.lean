import GhcCoreToLean.Parse

open GHCCore

private def validDump : String :=
  "{\"schemaVersion\":1,\"module\":\"Sample\",\"binds\":[]}"

#guard match parseVersionedProgramFromString validDump (some "Sample") with
  | .ok _ => true
  | .error _ => false

#guard match parseVersionedProgramFromString "{\"binds\":[]}" (some "Sample") with
  | .error "missing Core dump schemaVersion" => true
  | _ => false

#guard match parseVersionedProgramFromString
    "{\"schemaVersion\":2,\"module\":\"Sample\",\"binds\":[]}" (some "Sample") with
  | .error "unsupported Core dump schemaVersion: 2" => true
  | _ => false

#guard match parseVersionedProgramFromString validDump (some "Other") with
  | .error "Core dump module mismatch: expected Other, got Sample" => true
  | _ => false

#guard match parseVersionedProgramFromString "{\"binds\":[]}" none with
  | .ok _ => true
  | .error _ => false
