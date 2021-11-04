(*  Title:     JinjaDCI/Common/SystemClasses.thy

    Author:     Gerwin Klein, Susannah Mansky
    Copyright   2002 Technische Universitaet Muenchen, 2019-20 UIUC
    
    Based on the Jinja theory Common/SystemClasses.thy by Gerwin Klein
*)

section \<open> System Classes \<close>

theory SystemClasses
imports Decl Exceptions
begin

text \<open>
  This theory provides definitions for the @{text Object} class,
  and the system exceptions.
\<close>

definition ObjectC :: "'m cdecl"
where
  "ObjectC \<equiv> (Object, (undefined,[],[]))"

definition NullPointerC :: "'m cdecl"
where
  "NullPointerC \<equiv> (NullPointer, (Object,[],[]))"

definition ClassCastC :: "'m cdecl"
where
  "ClassCastC \<equiv> (ClassCast, (Object,[],[]))"

definition OutOfMemoryC :: "'m cdecl"
where
  "OutOfMemoryC \<equiv> (OutOfMemory, (Object,[],[]))"

definition NoClassDefFoundC :: "'m cdecl"
where
  "NoClassDefFoundC \<equiv> (NoClassDefFoundError, (Object,[],[]))"

definition IncompatibleClassChangeC :: "'m cdecl"
where
  "IncompatibleClassChangeC \<equiv> (IncompatibleClassChangeError, (Object,[],[]))"

definition NoSuchFieldC :: "'m cdecl"
where
  "NoSuchFieldC \<equiv> (NoSuchFieldError, (Object,[],[]))"

definition NoSuchMethodC :: "'m cdecl"
where
  "NoSuchMethodC \<equiv> (NoSuchMethodError, (Object,[],[]))"

definition SystemClasses :: "'m cdecl list"
where
  "SystemClasses \<equiv> [ObjectC, NullPointerC, ClassCastC, OutOfMemoryC, NoClassDefFoundC,
  IncompatibleClassChangeC, NoSuchFieldC, NoSuchMethodC]"

end
