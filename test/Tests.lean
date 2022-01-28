import Radiya.Ipld

import Tests.UnsignedVarint
import Tests.Multibase
import Tests.Multihash
import Tests.DagCbor

def main (args : List String) : IO UInt32 := do
  try
    IO.println "UnsignedVarint:"
    match Tests.UnsignedVarint.findFailing Tests.UnsignedVarint.cases with
    | [] => IO.println "✓ unsigned-varint"
    | xs => IO.println s!"𐄂 unsigned-varint: {xs}"
    IO.println "Multibase:"
    match Tests.Multibase.findFailing Tests.Multibase.Basic.cases with
    | [] => IO.println "✓ basic"
    | xs => IO.println s!"𐄂 basic: {xs}"
    match Tests.Multibase.findFailing Tests.Multibase.CaseInsensitivity.cases with
    | [] => IO.println "✓ case insensitivity"
    | xs => IO.println s!"𐄂 case insensitivity: {xs}"
    match Tests.Multibase.findFailing Tests.Multibase.LeadingZero.cases with
    | [] => IO.println "✓ leading zero"
    | xs => IO.println s!"𐄂 leading zero: {xs}"
    match Tests.Multibase.findFailing Tests.Multibase.TwoLeadingZeros.cases with
    | [] => IO.println "✓ two leading zeros"
    | xs => IO.println s!"𐄂 two leading zeros: {xs}"
    match Tests.Multibase.findFailing Tests.Multibase.RFC4648.cases with
    | [] => IO.println "✓ RFC 4648"
    | xs => IO.println s!"𐄂 RFC 4648: {xs}"
    IO.println "Multihash:"
    match Tests.Multihash.findFailing Tests.Multihash.cases with
    | [] => IO.println "✓ sha3-512"
    | xs => IO.println s!"𐄂 sha3-512: {xs}"
    pure 0
    IO.println "DagCbor:"
    match Tests.DagCbor.findFailing Tests.DagCbor.cases with
    | [] => IO.println "✓ DagCbor"
    | xs => IO.println s!"𐄂 DagCbor: {xs}"
    pure 0
  catch e =>
    IO.eprintln <| "error: " ++ toString e -- avoid "uncaught exception: ..."
    pure 1

