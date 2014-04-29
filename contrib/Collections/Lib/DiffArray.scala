

object DiffArray {

	import scala.collection.mutable.ArraySeq
	
	protected abstract sealed class DiffArray_D[A]
	final case class Current[A] (a:ArraySeq[A]) extends DiffArray_D[A]
	final case class Upd[A] (i:Int, v:A, n:DiffArray_D[A]) extends DiffArray_D[A]
	
	object DiffArray_Realizer {
		def realize[A](a:DiffArray_D[A]) : ArraySeq[A] = a match {
		  case Current(a) => ArraySeq.empty ++ a
		  case Upd(j,v,n) => {val a = realize(n); a.update(j, v); a}
		}
	}
	
	class T[A] (var d:DiffArray_D[A]) {
		
		def realize () = { val a=DiffArray_Realizer.realize(d); d = Current(a); a }
		override def toString() = realize().toSeq.toString
		
		override def equals(obj:Any) = 
			if (obj.isInstanceOf[T[A]])	obj.asInstanceOf[T[A]].realize().equals(realize())
			else false
		
	}
  
  
	def array_of_list[A](l : List[A]) : T[A] = new T(Current(ArraySeq.empty ++ l))
    def new_array[A](v:A, sz : BigInt) = new T[A](Current[A](ArraySeq.fill[A](sz.intValue)(v)))
  
    private def len[A](a:DiffArray_D[A]) : BigInt = a match {
	  case Current(a) => a.length
	  case Upd(_,_,n) => len(n)
	}
    
	def len[A](a : T[A]) : BigInt = len(a.d)
	
	private def sub[A](a:DiffArray_D[A], i:Int) : A = a match {
	  case Current(a) => a (i)
	  case Upd(j,v,n) => if (i==j) v else sub(n,i)
	}
	
	def get[A](a:T[A], i:BigInt) : A = sub(a.d,i.intValue)
  
	private def realize[A](a:DiffArray_D[A]) = DiffArray_Realizer.realize[A](a)
	
	def set[A](a:T[A], i:BigInt,v:A) : T[A] = a.d match {
	  case Current(ad) => { 
	    val ii = i.intValue; 
	    a.d = Upd(ii,ad(ii),a.d); 
	    //ad.update(ii,v);
	    ad(ii)=v
	    new T[A](Current(ad)) 
	  }
	  case Upd(_,_,_) => set(new T[A](Current(realize(a.d))), i.intValue,v)
	}
	  
	def grow[A](a:T[A], sz:BigInt, v:A) : T[A] = a.d match {
	  case Current(ad) => {
	    val adt = ArraySeq.fill[A](sz.intValue)(v)
	    System.arraycopy(ad.array, 0, adt.array, 0, ad.length);
	    new T[A](Current[A](adt))
	  }
	  case Upd (_,_,_) =>  {
	    val adt = ArraySeq.fill[A](sz.intValue)(v)
	    val ad = realize(a.d)
	    System.arraycopy(ad.array, 0, adt.array, 0, ad.length);
	    new T[A](Current[A](adt))
	  }
	}
	
	def shrink[A](a:T[A], sz:BigInt) : T[A] =
		if (sz==0) { 
			array_of_list(Nil)
		} else {
			a.d match {
				case Current(ad) => {
				    val v=ad(0);
				    val szz=sz.intValue
					val adt = ArraySeq.fill[A](szz)(v);
					System.arraycopy(ad.array, 0, adt.array, 0, szz);
					new T[A](Current[A](adt))
				}
				case Upd (_,_,_) =>  {
					val ad = realize(a.d);
				    val szz=sz.intValue
				    val v=ad(0);
					val adt = ArraySeq.fill[A](szz)(v);
					System.arraycopy(ad.array, 0, adt.array, 0, szz);
					new T[A](Current[A](adt))
				}
			}	  
		}
	
	def get_oo[A](d: => A, a:T[A], i:BigInt):A = try get(a,i) catch {
	  case _:scala.IndexOutOfBoundsException => d
	}
	
	def set_oo[A](d: Unit => T[A], a:T[A], i:BigInt, v:A) : T[A] = try set(a,i,v) catch {
	  case _:scala.IndexOutOfBoundsException => d ()
	}
	
}


object Test {
  
  
  
	def assert (b : Boolean) : Unit = if (b) () else throw new java.lang.AssertionError("Assertion Failed")
	  
	def eql[A] (a:DiffArray.T[A], b:List[A]) = assert (a.realize.corresponds(b)((x,y) => x.equals(y)))
	  

	def tests1(): Unit = {
		val a = DiffArray.array_of_list(1::2::3::4::Nil)
		  eql(a,1::2::3::4::Nil)
		
		// Simple update 
		val b = DiffArray.set(a,2,9)
		  eql(a,1::2::3::4::Nil)
		  eql(b,1::2::9::4::Nil)
		  
		// Another update
		val c = DiffArray.set(b,3,9)
		  eql(a,1::2::3::4::Nil)
		  eql(b,1::2::9::4::Nil)
		  eql(c,1::2::9::9::Nil)
		
		// Update of old version (forces realize)
		val d = DiffArray.set(b,2,8)
		  eql(a,1::2::3::4::Nil)
		  eql(b,1::2::9::4::Nil)
		  eql(c,1::2::9::9::Nil)
		  eql(d,1::2::8::4::Nil)
	  
  	}

	def tests2(): Unit = {
		val a = DiffArray.array_of_list(1::2::3::4::Nil)
		  eql(a,1::2::3::4::Nil)
		  
		// Simple update 
		val b = DiffArray.set(a,2,9)
		  eql(a,1::2::3::4::Nil)
		  eql(b,1::2::9::4::Nil)
		
		// Grow of current version
		val c = DiffArray.grow(b,6,9)
		  eql(a,1::2::3::4::Nil)
		  eql(b,1::2::9::4::Nil)
		  eql(c,1::2::9::4::9::9::Nil)

		// Grow of old version
		val d = DiffArray.grow(a,6,9)
		  eql(a,1::2::3::4::Nil)
		  eql(b,1::2::9::4::Nil)
		  eql(c,1::2::9::4::9::9::Nil)
		  eql(d,1::2::3::4::9::9::Nil)
		  
	}

	def tests3(): Unit = {
		val a = DiffArray.array_of_list(1::2::3::4::Nil)
		  eql(a,1::2::3::4::Nil)
		  
		// Simple update 
		val b = DiffArray.set(a,2,9)
		  eql(a,1::2::3::4::Nil)
		  eql(b,1::2::9::4::Nil)
		
		// Shrink of current version
		val c = DiffArray.shrink(b,3)
		  eql(a,1::2::3::4::Nil)
		  eql(b,1::2::9::4::Nil)
		  eql(c,1::2::9::Nil)

		// Shrink of old version
		val d = DiffArray.shrink(a,3)
		  eql(a,1::2::3::4::Nil)
		  eql(b,1::2::9::4::Nil)
		  eql(c,1::2::9::Nil)
		  eql(d,1::2::3::Nil)
	  
	}
	
	def tests4(): Unit = {
		val a = DiffArray.array_of_list(1::2::3::4::Nil)
		  eql(a,1::2::3::4::Nil)
		  
		// Update _oo (succeeds) 
		val b = DiffArray.set_oo((_) => a,a,2,9)
		  eql(a,1::2::3::4::Nil)
		  eql(b,1::2::9::4::Nil)

		// Update _oo (current version,fails) 
		val c = DiffArray.set_oo((_) => a,b,5,9)
		  eql(a,1::2::3::4::Nil)
		  eql(b,1::2::9::4::Nil)
		  eql(c,1::2::3::4::Nil)
		  
		// Update _oo (old version,fails) 
		val d = DiffArray.set_oo((_) => b,a,5,9)
		  eql(a,1::2::3::4::Nil)
		  eql(b,1::2::9::4::Nil)
		  eql(c,1::2::3::4::Nil)
		  eql(d,1::2::9::4::Nil)
		  
	}
	
	def tests5(): Unit = {
		val a = DiffArray.array_of_list(1::2::3::4::Nil)
		  eql(a,1::2::3::4::Nil)
		  
		// Update  
		val b = DiffArray.set(a,2,9)
		  eql(a,1::2::3::4::Nil)
		  eql(b,1::2::9::4::Nil)

		// Get_oo (current version, succeeds)
	    assert (DiffArray.get_oo(0,b,2)==9)
		// Get_oo (current version, fails)
	    assert (DiffArray.get_oo(0,b,5)==0)
		// Get_oo (old version, succeeds)
	    assert (DiffArray.get_oo(0,a,2)==3)
		// Get_oo (old version, fails)
	    assert (DiffArray.get_oo(0,a,5)==0)
		  
	}

	
	
	
	def main(args: Array[String]): Unit = {
		tests1 ()
		tests2 ()
		tests3 ()
		tests4 ()
		tests5 ()

		
		Console.println("Tests passed")
	}
  
}



