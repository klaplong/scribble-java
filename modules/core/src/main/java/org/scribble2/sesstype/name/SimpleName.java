package org.scribble2.sesstype.name;


// Make a subclass of CompoundName? Better for e.g. simple member name nodes?
public class SimpleName extends CompoundName
{
	private static final long serialVersionUID = 1L;

	//protected static final SimpleName EMPTY_NAME = new SimpleName();
	
	//public final String text;

	protected SimpleName(Kind kind)
	{
		super(kind);
		//this.text = "";
	}

	//public SimpleName(String text)
	public SimpleName(Kind kind, String text)
	{
		super(kind, text);
		//this.text = text;
	}
}
