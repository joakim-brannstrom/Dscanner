//          Copyright Brian Schott (Hackerpilot) 2012.
// Distributed under the Boost Software License, Version 1.0.
//    (See accompanying file LICENSE_1_0.txt or copy at
//          http://www.boost.org/LICENSE_1_0.txt)

module ctags;

import dparse.parser;
import dparse.lexer;
import dparse.ast;
import std.algorithm;
import std.range;
import std.stdio;
import std.array;
import std.conv;
import std.typecons;
import containers.ttree;

/**
 * Prints CTAGS information to the given file.
 * Includes metadata according to exuberant format used by Vim.
 * Params:
 *     output = the file that Exuberant TAGS info is written to
 *     fileNames = tags will be generated from these files
 */
void printCtags(File output, string[] fileNames)
{
	TTree!string tags;
	LexerConfig config;
	StringCache cache = StringCache(StringCache.defaultBucketCount);
	foreach (fileName; fileNames)
	{
		File f = File(fileName);
		if (f.size == 0)
			continue;
		auto bytes = uninitializedArray!(ubyte[])(to!size_t(f.size));
		f.rawRead(bytes);
		auto tokens = getTokensForParser(bytes, config, &cache);
		Module m = parseModule(tokens.array, fileName, null, &doNothing);

		auto printer = new CTagsPrinter(&tags);
		printer.fileName = fileName;
		printer.visit(m);
	}
	output.write("!_TAG_FILE_FORMAT\t2\n" ~ "!_TAG_FILE_SORTED\t1\n" ~ "!_TAG_FILE_AUTHOR\tBrian Schott\n"
			~ "!_TAG_PROGRAM_URL\thttps://github.com/Hackerpilot/Dscanner/\n");
	tags[].copy(output.lockingTextWriter);
}

private:

/// States determining how an access modifier affects tags when traversing the
/// AST.
/// The assumption is that there are fewer AST nodes and patterns that affects
/// the whole scope.
/// Therefor the default was chosen to be Reset.
enum AccessState
{
	Reset, /// when ascending the AST reset back to the previous access.
	Keep /// when ascending the AST keep the new access.
}

alias ScopeType = Tuple!(string, "type", string[], "path");
alias ContextType = Tuple!(ScopeType, "s", string, "access", bool, "insideStructClass");

void doNothing(string, size_t, size_t, string, bool)
{
}

string makeTag(Dec, E...)(Dec dec, string fileName, string kind, ScopeType scope_,
	auto ref E extra)
{
	return makeTag(dec.name.text, dec.name.line, fileName, kind, scope_, extra);
}

string makeTag(E...)(string tag, size_t line, string fileName, string kind,
	ScopeType scope_, auto ref E extra)
{
	string extra_;
	foreach (e; extra)
	{
		extra_ ~= "\t" ~ e;
	}
	string tagLine = "%s\t%s\t%d;\"\t%s\tline:%d%s%s\n".format(tag, fileName,
		line, kind, line, scopeToString(scope_), extra_);
	return tagLine;
}

ScopeType extendScope(ScopeType s0, string type, string path)
{
	return ScopeType(type, s0.path ~ path);
}

string scopeToString(ScopeType s)
{
	import std.array : join;

	if (s.type.length == 0)
		return "";

	return "\t" ~ s.type ~ ":" ~ join(s.path, ".");
}

string paramsToString(Dec)(const Dec dec)
{
	import dparse.formatter : Formatter;

	auto app = appender!string();
	auto formatter = new Formatter!(typeof(app))(app);

	static if (is(Dec == FunctionDeclaration) || is(Dec == Constructor))
	{
		formatter.format(dec.parameters);
	}
	else static if (is(Dec == TemplateDeclaration))
	{
		formatter.format(dec.templateParameters);
	}

	return app.data;
}

final class CTagsPrinter : ASTVisitor
{
	public this(TTree!string* output)
	{
		this.tagLines = output;
	}

	override void visit(const ClassDeclaration dec)
	{
		tagLines.insert(makeTag(dec, fileName, "c", context.s, context.access));
		auto c = context;
		context.s = extendScope(context.s, "class", dec.name.text);
		context.access = "access:public";
		context.insideStructClass = true;
		dec.accept(this);
		context = c;
	}

	override void visit(const StructDeclaration dec)
	{
		// anonymous struct, skipping
		if (dec.name == tok!"")
		{
			dec.accept(this);
			return;
		}
		tagLines.insert(makeTag(dec, fileName, "s", context.s, context.access));
		auto c = context;
		context.s = extendScope(context.s, "struct", dec.name.text);
		context.access = "access:public";
		context.insideStructClass = true;
		dec.accept(this);
		context = c;
	}

	override void visit(const InterfaceDeclaration dec)
	{
		tagLines.insert(makeTag(dec, fileName, "i", context.s, context.access));
		auto c = context;
		context.s = extendScope(context.s, "class", dec.name.text);
		context.access = context.access;
		context.insideStructClass = false;
		dec.accept(this);
		context = c;
	}

	override void visit(const TemplateDeclaration dec)
	{
		auto params = paramsToString(dec);

		tagLines.insert(makeTag(dec, fileName, "T", context.s, context.access, "signature:" ~ params));
		context.s = extendScope(context.s, "template", dec.name.text);
		context.access = context.access;
		context.insideStructClass = false;
		dec.accept(this);
	}

	override void visit(const FunctionDeclaration dec)
	{
		auto params = paramsToString(dec);

		tagLines.insert(makeTag(dec, fileName, "f", context.s, context.access, "signature:" ~ params));
	}

	override void visit(const Constructor dec)
	{
		auto params = paramsToString(dec);

		tagLines.insert(makeTag("this", dec.line, fileName, "f", context.s,
			context.access, "signature:" ~ params));
	}

	override void visit(const Destructor dec)
	{
		tagLines.insert(makeTag("~this", dec.line, fileName, "f", context.s, context.access));
	}

	override void visit(const EnumDeclaration dec)
	{
		tagLines.insert(makeTag(dec, fileName, "g", context.s, context.access));
		auto c = context;
		context.s = extendScope(context.s, "enum", dec.name.text);
		context.access = context.access;
		dec.accept(this);
		context = c;
	}

	override void visit(const UnionDeclaration dec)
	{
		if (dec.name == tok!"")
		{
			dec.accept(this);
			return;
		}
		tagLines.insert(makeTag(dec, fileName, "u", context.s, context.access));
		auto c = context;
		context.s = extendScope(context.s, "union", dec.name.text);
		context.access = context.access;
		dec.accept(this);
		context = c;
	}

	override void visit(const AnonymousEnumMember dec)
	{
		tagLines.insert(makeTag(dec, fileName, "e", context.s, context.access));
	}

	override void visit(const EnumMember dec)
	{
		tagLines.insert(makeTag(dec, fileName, "e", context.s, context.access));
	}

	override void visit(const VariableDeclaration dec)
	{
		string tagname = "v";
		if (context.insideStructClass)
		{
			tagname = "m";
		}

		foreach (d; dec.declarators)
		{
			tagLines.insert(makeTag(d, fileName, tagname, context.s, context.access));
		}
		dec.accept(this);
	}

	override void visit(const AutoDeclaration dec)
	{
		foreach (i; dec.identifiers)
		{
			tagLines.insert(makeTag(i.text, i.line, fileName, "v", context.s, context.access));
		}
		dec.accept(this);
	}

	override void visit(const Invariant dec)
	{
		tagLines.insert(makeTag("invariant", dec.line, fileName, "v", context.s, context.access));
	}

	override void visit(const ModuleDeclaration dec)
	{
		context.s = ScopeType();
		context.access = "access:public";
		context.insideStructClass = false;
		dec.accept(this);
	}

	override void visit(const Attribute attribute)
	{
		if (attribute.attribute != tok!"")
		{
			switch (attribute.attribute.type)
			{
			case tok!"export":
				context.access = "access:public";
				break;
			case tok!"public":
				context.access = "access:public";
				break;
			case tok!"package":
				context.access = "access:protected";
				break;
			case tok!"protected":
				context.access = "access:protected";
				break;
			case tok!"private":
				context.access = "access:private";
				break;
			default:
			}
		}

		attribute.accept(this);
	}

	override void visit(const AttributeDeclaration dec)
	{
		accessSt = AccessState.Keep;
		dec.accept(this);
	}

	override void visit(const Declaration dec)
	{
		auto c = context;
		dec.accept(this);

		final switch (accessSt) with (AccessState)
		{
		case Reset:
			context = c;
			break;
		case Keep:
			break;
		}
		accessSt = AccessState.Reset;
	}

	override void visit(const Unittest dec)
	{
		// skipping symbols inside a unit test to not clutter the ctags file
		// with "temporary" symbols.
		// TODO when phobos have a unittest library investigate how that could
		// be used to describe the tests.
		// Maybe with UDA's to give the unittest a "name".
	}

	override void visit(const AliasDeclaration dec)
	{
		// Old style alias
		if (dec.identifierList)
		{
			foreach (i; dec.identifierList.identifiers)
			{
				tagLines.insert(makeTag(i.text, i.line, fileName, "a", context.s, context.access));
			}
		}
		dec.accept(this);
	}

	override void visit(const AliasInitializer dec)
	{
		tagLines.insert(makeTag(dec, fileName, "a", context.s, context.access));

		dec.accept(this);
	}

	override void visit(const AliasThisDeclaration dec)
	{
		auto name = dec.identifier;
		tagLines.insert(makeTag(name.text, name.line, fileName, "a", context.s, context.access));

		dec.accept(this);
	}

	alias visit = ASTVisitor.visit;
	string fileName;
	TTree!string* tagLines;
	ContextType context;
	AccessState accessSt;
}
