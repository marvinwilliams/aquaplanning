package edu.kit.aquaplanning.util;

/**
 * A generic pair of objects of differing class type. Can be used to make a
 * method return a pair of objects in a type-safe way.
 */
public class Pair<A, B> {

  private A left;
  private B right;

  /**
   * Creates a data pair out of the two provided objects.
   */
  public Pair(A left, B right) {
    this.left = left;
    this.right = right;
  }

  /**
   * Returns the left object in the pair.
   */
  public A getLeft() {
    return left;
  }

  /**
   * Returns the right object in the pair.
   */
  public B getRight() {
    return right;
  }

  public @Override boolean equals(Object obj) {
    if (this == obj) {
      return true;
    }
    if (obj == null) {
      return false;
    }
    if (obj.getClass() != getClass()) {
      return false;
    }
    Pair<A, B> pair = (Pair<A, B>) obj;
    return pair.getLeft().equals(getLeft()) && pair.getRight().equals(getRight());
  }

  @Override
  public String toString() {
    return "( " + left.toString() + ", " + right.toString() + " )";
  }
}
