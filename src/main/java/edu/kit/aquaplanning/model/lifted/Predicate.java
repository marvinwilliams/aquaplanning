package edu.kit.aquaplanning.model.lifted;

import java.util.ArrayList;
import java.util.List;

public class Predicate {

	protected String name;
	private List<Type> argumentTypes;
	
	public Predicate(String name) {
		this.name = name;
		this.argumentTypes = new ArrayList<>();
	}
	
	public void addArgumentType(Type type) {
		this.argumentTypes.add(type);
	}
	
	public String getName() {
		return name;
	}
	
	public List<Type> getArgumentTypes() {
		return argumentTypes;
	}
	
	public int getNumArgs() {
		return argumentTypes.size();
	}
	
	@Override
	public String toString() {
		String out = "";
		out += name + "( ";
		for (Type type : argumentTypes) {
			out += type.getName() + " ";
		}
		out += ")";
		return out;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((argumentTypes == null) ? 0 : argumentTypes.hashCode());
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Predicate other = (Predicate) obj;
		if (argumentTypes == null) {
			if (other.argumentTypes != null)
				return false;
		} else if (!argumentTypes.equals(other.argumentTypes))
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		return true;
	}
}
