class  {:autocontracts} Stack
{
    ghost var conteudo:seq<int>;
    ghost var max:nat;

    var arr:array<int>;
    var index:nat;

    predicate Valid()
    {
        index <= arr.Length
        &&
        |arr[..index]| == |conteudo| 
        && 
        arr[..index] == conteudo
    }

    constructor (tamanho:nat)
    ensures is_Empty(conteudo)
    ensures max == tamanho

    method toogleStack()
    ensures isReversed(conteudo,old(conteudo))
    ensures max == old(max)

    method push(v:int) returns (r:bool)
    ensures r == !is_Full(old(conteudo))
    ensures r == false ==> conteudo == old(conteudo)
    ensures r == true ==> checkStack(old(conteudo),conteudo,v)
    ensures max == old(max)

    method pop() returns (r:int)
    requires !is_Empty(conteudo)
    ensures checkStack(conteudo,old(conteudo),r)
    ensures max == old(max)

    method numberOfElements() returns (r:nat)
    ensures r == |conteudo|
    ensures conteudo == old(conteudo)
    ensures max == old(max)

    method maxOfElements() returns (r:nat)
    ensures r == max
    ensures conteudo == old(conteudo)
    ensures max == old(max)

    method isEmpty() returns (r:bool)
    ensures r == is_Empty(conteudo)
    ensures conteudo == old(conteudo)
    ensures max == old(max)

    method isFull() returns (r:bool)
    ensures r == is_Full(conteudo) 
    ensures conteudo == old(conteudo)
    ensures max == old(max)

    predicate is_Empty(cont:seq<int>)
    {
        |cont| == 0
    }

    predicate is_Full(cont:seq<int>)
    {
        |cont| == max
    }

    predicate isLastElement(v:int,cont:seq<int>)
    requires |cont| > 0
    {
        v == cont[|cont|-1]
    }

    predicate checkStack(s1:seq<int>,s2:seq<int>,v:int)
    {
        |s1| == |s2|-1
        &&
        s1 == s2[..|s2|-1]
        &&
        isLastElement(v,s2)
    }

    predicate permutacao(a:seq<int>,b:seq<int>)
    {
        multiset(a) == multiset(b)
    }

    predicate isReversed(s1:seq<int>,s2:seq<int>)
    {
        |s1| == |s2|
        &&
        forall k :: 0 <= k < |s1| ==> s1[k] == s2[|s2| - 1 - k]
    }
}

method Main2()
{
    var max := 0;
    var rBool:bool;
    var rNat:nat;
    var rInt:nat;

    max := 5;
    var s2 := new Stack(max);

    rBool := s2.push(4);
    assert rBool == true;
    assert s2.conteudo == [4];

    rBool := s2.push(3);
    assert rBool == true;
    assert s2.conteudo == [4,3];

    rBool := s2.push(2);
    assert rBool == true;
    assert s2.conteudo == [4,3,2];

    rBool := s2.push(1);
    assert rBool == true;

    rBool := s2.push(1);
    assert rBool == true;

    rInt := s2.pop();   
    assert rInt == 1;

    assert s2.conteudo == [4,3,2,1];
    s2.toogleStack();
    assert s2.conteudo == [1,2,3,4];

    rInt := s2.pop();
    assert rInt == 4;
    assert s2.conteudo == [1,2,3];

    rInt := s2.pop();
    assert rInt == 3;

    rInt := s2.pop();
    assert rInt == 2;

    rInt := s2.pop();
    assert rInt == 1;
}

method Main1()
{
    var max := 0;
    var rBool:bool;
    var rNat:nat;
    var rInt:nat;

    max := 0;
    var s1 := new Stack(max);

    rBool := s1.push(3);
    assert rBool == false;

    rNat := s1.maxOfElements();
    assert rNat == 0;

    rNat := s1.numberOfElements();
    assert rNat == 0;

    rBool := s1.isEmpty();
    assert rBool;

    rBool :=  s1.isFull();
    assert rBool;
}

method Main3()
{
    var max := 0;
    var rBool:bool;
    var rNat:nat;
    var rInt:nat;

    max := 5;
    var s3 := new Stack(max);

    rBool := s3.push(3);
    assert rBool == true;

    rNat := s3.maxOfElements();
    assert rNat == 5;

    rNat := s3.numberOfElements();
    assert rNat == 1;

    rBool := s3.isEmpty();
    assert rBool == false;

    rBool :=  s3.isFull();
    assert rBool == false;

    rInt := s3.pop();
    assert rInt == 3;
}
