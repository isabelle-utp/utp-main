header {* Functrans simpset for Code Preprocessing *}
theory Ord_Code_Preproc
imports Main ICF_Tools
begin

ML {*
  signature ORD_CODE_PREPROC = sig
    val add: int * string * (theory -> thm -> thm) -> theory -> theory
    val rem: string -> theory -> theory

    val get: theory -> (int * string * (theory -> thm -> thm)) list

    val setup: theory -> theory
    val trace_enabled: bool Unsynchronized.ref
  end


  structure Ord_Code_Preproc: ORD_CODE_PREPROC = struct
    val trace_enabled = Unsynchronized.ref false

    val do_sort = sort (rev_order o int_ord o pairself #1)

    structure Data = Theory_Data (
      type T = (int * string * (theory -> thm -> thm)) list
      val empty = []
      val extend = I
      val merge = op @ #> do_sort #> distinct (op = o pairself #2)
    );

    val get = Data.get

    fun add tr = Data.map (fn l => do_sort (tr::l))

    fun rem name = Data.map (filter (fn (_,n,_) => n <>name))

    
    local
      fun trace_ft ft thy thms = if !trace_enabled then let
        val res = ft thy thms;
        val (m1,m2) = case res of NONE => ("NF: ","")
        | SOME thms => ("Preproc: REW: "," --> " ^ PolyML.makestring thms);

        val _ = tracing (m1 ^ PolyML.makestring thms ^ m2);
      in res end
      else ft thy thms;

      fun s_functrans thy thms = let
        val trs = Data.get thy;
        val process = fold (fn (_,_,tr) => fn thm => tr thy thm) trs;
        val process' = fold (fn (_,name,tr) => fn thm => let
            val thm' = tr thy thm;
            val _ = if !trace_enabled andalso not (Thm.eq_thm (thm,thm')) then
              tracing ("Preproc "^name^": "^PolyML.makestring thm ^ " --> " ^
                PolyML.makestring thm')
            else ();
          in thm' end
        ) trs;

        fun rew_ch acc ch [] = if ch then SOME acc else NONE
        | rew_ch acc ch (thm::thms) = let
          val thm' = process' thm;
          val ch = ch orelse not (Thm.eq_thm (thm,thm'));
        in rew_ch (thm'::acc) ch thms end;
      in
        rew_ch [] false thms
      end;
    in
      val functrans = ("Functrans_ss.functrans",
        Code_Preproc.simple_functrans ((*trace_ft*) (s_functrans)));
    end;

    val setup = Code_Preproc.add_functrans functrans;

  end

  signature OC_SIMPSET = sig
    val get: theory -> simpset
    val map: (simpset -> simpset) -> theory -> theory
    val setup: theory -> theory
  end

  functor Oc_Simpset(val prio:int val name:string): OC_SIMPSET = struct
    structure Data = Theory_Data (
      type T = simpset
      val empty = empty_ss
      val extend = I
      val merge = Raw_Simplifier.merge_ss
    );

    val get = Data.get
    val map = Data.map

    local 
      fun trans_fun thy thm = let
        val ss = get thy |> Raw_Simplifier.global_context thy
      in simplify ss thm end;
    in
      val setup = Ord_Code_Preproc.add (prio, name, trans_fun);
    end

  end


*}

setup Ord_Code_Preproc.setup

end
