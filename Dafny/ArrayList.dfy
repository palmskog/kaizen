module Collections {

  class ArrayList<T> {

    var arr: array<T>;
    var size: int;

    ghost var list: seq<T>;
    ghost var Repr: set<object>;

    predicate Valid() 
      reads this, Repr;
    {
      Repr == {this, arr} &&
      |list| == size &&
      size <= arr.Length &&
      forall i :: 0 <= i < size ==> arr[i] == list[i]
    }

    constructor()
      ensures Valid() && fresh(Repr);
      ensures size == 0;
      ensures list == [];
      ensures arr.Length == 0;
    {
      Repr := {this};
      arr := new T[0];
      size := 0;
      list := [];
      Repr := Repr + {arr};
    }

    constructor InitialCapacity(initialCapacity: int, archetype: T)
      requires initialCapacity >= 0;
      ensures Valid() && fresh(Repr);
      ensures size == 0;
      ensures list == [];
      ensures arr.Length == initialCapacity;
    {
      Repr := {this};
      arr := new T[initialCapacity](_ => archetype);
      size := 0;
      list := [];
      Repr := Repr + {arr};
    }

    method Size() returns (lSize: int)
      requires Valid();
      ensures lSize == |list|;
    {
      lSize := size;
    }

    method IsEmpty() returns (lEmpty: bool)
      requires Valid();
      ensures Valid();
      ensures lEmpty <==> |list| == 0;
    {
      lEmpty := size == 0;
    }

    method Get(index: int) returns (element: T)
      requires Valid();
      requires 0 <= index < size;
      ensures element == list[index];
    {
      element := arr[index];
    }

    /*
    method Insert(index: int, element: T)
      modifies Repr;
      requires Valid();
      requires 0 <= index < size;
      ensures size == old(size) + 1;
      //ensures list == old(list[0..index]) + [element] + old(list[index..size]);
      //ensures list[index] == element;
      //ensures forall k :: 0 <= k < index ==> list[k] == old(list[k]);
      //ensures forall k :: index + 1 <= k < size ==> list[k] == old(list[k-1]);
      ensures old(arr.Length) < old(size) + 1 ==> fresh(Repr - {this}) && arr.Length >= old(size) + 1;
      ensures old(arr.Length) >= old(size) + 1 ==> Repr == old(Repr);
    {
      EnsureCapacity(size + 1, element);
      var i := index;
      var curr := element;
      while i < size
        invariant index <= i <= size;
      {
        var next := arr[i];
        arr[i] := curr;
        curr := next;
        i := i + 1;
      }
      size := size + 1;
    }
    */

    method Remove(index: int)
      modifies Repr;
      requires Valid();
      requires 0 <= index < size;
      ensures Valid();
      ensures size == old(size) - 1;
      ensures list == old(list[0..index]) + old(list[index + 1..size]);
      ensures forall k :: 0 <= k < index ==> list[k] == old(list[k]);
      ensures forall k :: index <= k < size ==> list[k] == old(list[k + 1]);
      ensures Repr == old(Repr);
    {
      ghost var l := list[0..index];
      var i := index;
      while i < size - 1
        modifies arr;
        invariant index <= i < size;
        invariant |l| == i;
        invariant l == list[0..index] + list[index + 1..i + 1];
        invariant forall j :: index <= j < i ==> arr[j] == old(arr[j+1])
        invariant forall j :: 0 <= j < i ==> arr[j] == l[j];
        invariant forall j :: i < j < arr.Length ==> arr[j] == old(arr[j]);
      {
        arr[i] := arr[i+1];
        l := l + [arr[i]];
        i := i + 1;
      }
      list := l;
      size := size - 1;
    }

    method Add(element: T) returns (index: int)
      modifies Repr;
      requires Valid();
      ensures Valid();
      ensures size == old(size) + 1;
      ensures index == old(size);
      ensures list[index] == element;
      ensures list == old(list) + [element];
      ensures forall k :: 0 <= k < index ==> list[k] == old(list[k]);
      ensures old(arr.Length) < old(size) + 1 ==> fresh(Repr - {this}) && arr.Length >= old(size) + 1;
      ensures old(arr.Length) >= old(size) + 1 ==> Repr == old(Repr);
    {
      EnsureCapacity(size + 1, element);
      arr[size] := element;
      list := list + [element];
      index := size;
      size := size + 1;
    }

    method EnsureCapacity(minCapacity: int, archetype: T)
      modifies Repr;
      requires Valid();
      ensures Valid();
      ensures list == old(list);
      ensures minCapacity > old(arr.Length) ==> fresh(Repr - {this});
      ensures minCapacity <= old(arr.Length) ==> Repr == old(Repr);
      ensures arr.Length >= minCapacity;
    {
      var oldCapacity := arr.Length;
      if minCapacity > oldCapacity {
        var newCapacity := (oldCapacity * 3)/2 + 1;
        if (newCapacity < minCapacity) {
          newCapacity := minCapacity;
        }
        var size', arr' := size, arr;
        var newArr := new T[newCapacity](i reads arr' requires 0 <= i => if i < size' then arr'[i] else archetype);
        Repr := Repr - {arr} + {newArr};
        arr := newArr;
      }
    }

    method Append(a: ArrayList<T>)
      modifies Repr;
      requires Valid();
      requires a.Valid();
      requires Repr !! a.Repr;
      ensures Valid();
      ensures size == old(size) + a.size;
      ensures list == old(list) + a.list;
      ensures forall k :: 0 <= k < old(size) ==> list[k] == old(list[k]);
      ensures forall k :: 0 <= k < a.size ==> list[old(size) + k] == a.list[k];
      ensures old(arr.Length) < old(size) + a.size ==> fresh(Repr - {this});
      ensures old(arr.Length) >= old(size) + a.size ==> Repr == old(Repr);
    {
      var numNew := a.size;
      if numNew != 0 {
        EnsureCapacity(size + numNew, a.arr[0]);
        ArrayCopy(a.arr, 0, arr, size, numNew);
        list := list + a.list;
        size := size + numNew;
      }
    }

  }

  iterator ListIterator<T>(l: ArrayList<T>) yields (x: T)
    requires l.Valid();
    reads l.Repr;
    yield ensures |xs| <= |l.list|;
    yield ensures xs == l.list[..|xs|];
    yield ensures x == l.list[|xs|-1];
    ensures Valid();
    ensures xs == l.list;
  {
    var i := 0;
    while i < l.size
      invariant i <= l.size;
      invariant xs == l.list[..i];
    {
      yield l.arr[i];
      i := i + 1;
    }
  }

  method ArrayCopy<T>(src:array<T>, srcIndex:int, dst:array<T>, dstIndex:int, len:int)
    modifies dst;
    requires src != dst;
    requires 0 <= len;
    requires 0 <= srcIndex && srcIndex + len <= src.Length;
    requires 0 <= dstIndex && dstIndex + len <= dst.Length;
    ensures forall k :: 0 <= k < dstIndex ==> dst[k] == old(dst[k]);
    ensures forall k :: dstIndex <= k < dstIndex + len ==> dst[k] == src[k - dstIndex + srcIndex];
    ensures forall k :: dstIndex + len <= k < dst.Length ==> dst[k] == old(dst[k]);
    ensures forall k :: srcIndex <= k < srcIndex + len ==> src[k] == dst[k - srcIndex + dstIndex];
  {
    var i := 0;
    while i < len
      invariant 0 <= dstIndex && dstIndex + i <= dst.Length;
      invariant 0 <= srcIndex && srcIndex + i <= src.Length;
      invariant forall k :: 0 <= k < dstIndex ==> dst[k] == old(dst[k]);
      invariant forall k :: dstIndex <= k < dstIndex + i ==> dst[k] == src[k - dstIndex + srcIndex];
      invariant forall k :: dstIndex + len <= k < dst.Length ==> dst[k] == old(dst[k]);
    {
      dst[dstIndex + i]  := src[srcIndex + i];
      i := i + 1;
    }
  }

}
