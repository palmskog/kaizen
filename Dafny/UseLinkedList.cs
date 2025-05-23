using System;
using Collections;
 
public class UseLinkedList
{
    public static void Main()
    {
	Console.WriteLine("creating singleton list");
	var l1 = new Node<int>();
	l1.Singleton(3);
	Console.WriteLine("inserting into singleton list");
	var l2 = new Node<int>();
	l2.Insert(4, l1);

	var l3 = new Node<int>();
	l3.Singleton(0);

	Node<int> l4;
	Node<int>.Append_k(l2, l3, out l4);

	Node<int> l5;
	Node<int>.Append(l4, l3, out l5);
    }
}
