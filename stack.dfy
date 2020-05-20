class  {:autocontracts} Stack
{
    ghost var conteudo:seq<int>;
    ghost var max:nat;

    var arr:array<int>;
    var index:nat;

    predicate Valid()
    {
        arr.Length > 0
        &&
        max == arr.Length
        &&
        0 <= index <= arr.Length
        &&
        index == |conteudo|
        && 
        arr[..index] == conteudo
    }

    constructor (tamanho:nat)
    requires tamanho > 0
    ensures |conteudo| == 0
    ensures max == tamanho
    {
        arr := new int[tamanho];
        max := tamanho;
        index := 0;
        conteudo := [];
    }

    method toogleStack()
    ensures |conteudo| == |old(conteudo)|
    ensures isReversed(conteudo,old(conteudo))
    ensures multiset(conteudo) == multiset(old(conteudo))
    ensures old(max) == max && index == old(index)
    {
        if arr.Length < 2
        {
            return;
        }

        var newArr := new int[arr.Length];
        forall(k | 0 <= k < index)
        {
            newArr[k] := arr[index-1-k];
        }
        var s1,s2 := newArr[..index],arr[..index];
        assert multiset(s1) == multiset(s2);

        arr := newArr;
        conteudo := arr[0..index];
    }

    method push(v:int) returns (r:bool)
    ensures r == (|old(conteudo)| < max)
    ensures r == false ==> conteudo == old(conteudo)
    ensures r == true ==> conteudo == (old(conteudo) + [v]) && v == conteudo[|conteudo|-1]
    ensures old(max) == max
    {
        r := index < arr.Length;
        if r
        {
            arr[index] := v;
            index := index + 1;
            conteudo := arr[..index];
        }
    }

    method pop() returns (r:int)
    requires |conteudo| > 0
    ensures r == old(conteudo)[|old(conteudo)|-1]
    ensures old(conteudo)[..(|old(conteudo)|-1)] == conteudo
    ensures old(max) == max
    {
        index := index - 1;
        r := arr[index];
        conteudo := conteudo[..index];
    }

    method numberOfElements() returns (r:nat)
    ensures r == |conteudo|
    ensures conteudo == old(conteudo)
    ensures old(max) == max
    {
        return index;
    }

    method maxOfElements() returns (r:nat)
    ensures r == max
    ensures conteudo == old(conteudo)
    ensures old(max) == max
    {
        r := arr.Length;
    }

    method isEmpty() returns (r:bool)
    ensures r == (|conteudo| == 0)
    ensures conteudo == old(conteudo)
    ensures old(max) == max
    {
        return index == 0;
    }

    method isFull() returns (r:bool)
    ensures r == (|conteudo| == max)
    ensures conteudo == old(conteudo)
    ensures old(max) == max
    {
        return index == arr.Length;
    }

    predicate isReversed(s1:seq<int>,s2:seq<int>)
    {
        |s1| == |s2|
        &&
        forall k :: 0 <= k < |s1| ==> s1[k] == s2[|s2| - 1 - k]
    }
}

method Main0()
{
    var max := 3;
    var rBool:bool;
    var rNat:nat;
    var rInt:int;

    // init

    var s := new Stack(max);

    rNat := s.maxOfElements();
    assert rNat == max;

    rNat := s.numberOfElements();
    assert rNat == 0;

    rBool := s.isEmpty();
    assert rBool;

    rBool :=  s.isFull();
    assert rBool == false;

    // Push

    rBool := s.push(3);
    assert rBool == true;
    assert s.conteudo == [3];

    rNat := s.numberOfElements();
    assert rNat == 1;

    rBool := s.isEmpty();
    assert rBool == false;

    rBool :=  s.isFull();
    assert rBool == false;

    rNat := s.maxOfElements();
    assert rNat == max;

    rBool := s.push(4);
    rBool := s.push(1);
    assert s.conteudo == [3,4,1];

    rBool :=  s.isFull();
    assert rBool == true;

    rBool := s.push(5);
    assert rBool == false;
    assert s.conteudo == [3,4,1];

    // Pop

    rInt := s.pop();
    assert rInt == 1;
    assert s.conteudo == [3,4];

    rNat := s.numberOfElements();
    assert rNat == 2;

    rBool := s.isEmpty();
    assert rBool == false;

    rBool :=  s.isFull();
    assert rBool == false;

    rNat := s.maxOfElements();
    assert rNat == max;
}

method Main1()
{
    var max := 5;
    var rBool:bool;
    var rNat:nat;
    var rInt:nat;

    var s2 := new Stack(max);

    rBool := s2.push(4);
    rBool := s2.push(3);
    rBool := s2.push(2);
    rBool := s2.push(1);
    rBool := s2.push(1);
    rInt := s2.pop();   
    assert s2.conteudo == [4,3,2,1];

    s2.toogleStack();
    assert s2.conteudo == [1,2,3,4];
}
