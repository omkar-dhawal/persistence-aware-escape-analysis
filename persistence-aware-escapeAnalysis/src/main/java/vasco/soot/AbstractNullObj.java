/**
 * 
 */
package vasco.soot;

import soot.RefType;
import soot.Type;
import soot.jimple.internal.AbstractNewExpr;

/**
 * @author shashin
 *
 */
@SuppressWarnings("serial")
public class AbstractNullObj extends AbstractNewExpr {

	@Override
	public Object clone() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String toString() {
		return "NULL";
	}

	@Override
	  public RefType getBaseType() {
	    return super.getBaseType();
	  }

	@Override
	  public void setBaseType(RefType type) {
	    super.setBaseType(type);
	  }
	
	@Override
	  public Type getType() {
	    return super.getType();
	  }

}
