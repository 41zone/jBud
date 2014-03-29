(function(window,undefined){
	var jBud = function(selector,context){
		return new jBud.seed.instance(selector,context);
	};
	jBud.description = {
			version:"0.9",//当前版本
			founder:"Jimmy Song",//创始人
			compatible:"0.9"//向后兼容
	};
	jBud.hi = function() {
		var d = jBud.description;
		if(window.console) {
			console.log("version : ",d.version,", author : ",d.founder);
		} else {
			alert("version : "+d.version+", author : "+d.founder);
		}
	};
	window.jBud = jBud;
	(function( window ) {
	var i,
		support,
		cachedruns,
		Expr,
		getText,
		isXML,
		compile,
		outermostContext,
		sortInput,
		hasDuplicate,
	
		// Local document vars
		setDocument,
		document,
		docElem,
		documentIsHTML,
		rbuggyQSA,
		rbuggyMatches,
		matches,
		contains,
	
		// Instance-specific data
		expando = "sizzle" + -(new Date()),
		preferredDoc = window.document,
		dirruns = 0,
		done = 0,
		classCache = createCache(),
		tokenCache = createCache(),
		compilerCache = createCache(),
		sortOrder = function( a, b ) {
			if ( a === b ) {
				hasDuplicate = true;
			}
			return 0;
		},
	
		// General-purpose constants
		strundefined = typeof undefined,
		MAX_NEGATIVE = 1 << 31,
	
		// Instance methods
		hasOwn = ({}).hasOwnProperty,
		arr = [],
		pop = arr.pop,
		push_native = arr.push,
		push = arr.push,
		slice = arr.slice,
		// Use a stripped-down indexOf if we can't use a native one
		indexOf = arr.indexOf || function( elem ) {
			var i = 0,
				len = this.length;
			for ( ; i < len; i++ ) {
				if ( this[i] === elem ) {
					return i;
				}
			}
			return -1;
		},
	
		booleans = "checked|selected|async|autofocus|autoplay|controls|defer|disabled|hidden|ismap|loop|multiple|open|readonly|required|scoped",
	
		// Regular expressions
	
		// Whitespace characters http://www.w3.org/TR/css3-selectors/#whitespace
		whitespace = "[\\x20\\t\\r\\n\\f]",
		// http://www.w3.org/TR/css3-syntax/#characters
		characterEncoding = "(?:\\\\.|[\\w-]|[^\\x00-\\xa0])+",
	
		// Loosely modeled on CSS identifier characters
		// An unquoted value should be a CSS identifier http://www.w3.org/TR/css3-selectors/#attribute-selectors
		// Proper syntax: http://www.w3.org/TR/CSS21/syndata.html#value-def-identifier
		identifier = characterEncoding.replace( "w", "w#" ),
	
		// Acceptable operators http://www.w3.org/TR/selectors/#attribute-selectors
		attributes = "\\[" + whitespace + "*(" + characterEncoding + ")" + whitespace +
			"*(?:([*^$|!~]?=)" + whitespace + "*(?:(['\"])((?:\\\\.|[^\\\\])*?)\\3|(" + identifier + ")|)|)" + whitespace + "*\\]",
	
		// Prefer arguments quoted,
		//   then not containing pseudos/brackets,
		//   then attribute selectors/non-parenthetical expressions,
		//   then anything else
		// These preferences are here to reduce the number of selectors
		//   needing tokenize in the PSEUDO preFilter
		pseudos = ":(" + characterEncoding + ")(?:\\(((['\"])((?:\\\\.|[^\\\\])*?)\\3|((?:\\\\.|[^\\\\()[\\]]|" + attributes.replace( 3, 8 ) + ")*)|.*)\\)|)",
	
		// Leading and non-escaped trailing whitespace, capturing some non-whitespace characters preceding the latter
		rtrim = new RegExp( "^" + whitespace + "+|((?:^|[^\\\\])(?:\\\\.)*)" + whitespace + "+$", "g" ),
	
		rcomma = new RegExp( "^" + whitespace + "*," + whitespace + "*" ),
		rcombinators = new RegExp( "^" + whitespace + "*([>+~]|" + whitespace + ")" + whitespace + "*" ),
	
		rattributeQuotes = new RegExp( "=" + whitespace + "*([^\\]'\"]*)" + whitespace + "*\\]", "g" ),
	
		rpseudo = new RegExp( pseudos ),
		ridentifier = new RegExp( "^" + identifier + "$" ),
	
		matchExpr = {
			"ID": new RegExp( "^#(" + characterEncoding + ")" ),
			"CLASS": new RegExp( "^\\.(" + characterEncoding + ")" ),
			"TAG": new RegExp( "^(" + characterEncoding.replace( "w", "w*" ) + ")" ),
			"ATTR": new RegExp( "^" + attributes ),
			"PSEUDO": new RegExp( "^" + pseudos ),
			"CHILD": new RegExp( "^:(only|first|last|nth|nth-last)-(child|of-type)(?:\\(" + whitespace +
				"*(even|odd|(([+-]|)(\\d*)n|)" + whitespace + "*(?:([+-]|)" + whitespace +
				"*(\\d+)|))" + whitespace + "*\\)|)", "i" ),
			"bool": new RegExp( "^(?:" + booleans + ")$", "i" ),
			// For use in libraries implementing .is()
			// We use this for POS matching in `select`
			"needsContext": new RegExp( "^" + whitespace + "*[>+~]|:(even|odd|eq|gt|lt|nth|first|last)(?:\\(" +
				whitespace + "*((?:-\\d)?\\d*)" + whitespace + "*\\)|)(?=[^-]|$)", "i" )
		},
	
		rinputs = /^(?:input|select|textarea|button)$/i,
		rheader = /^h\d$/i,
	
		rnative = /^[^{]+\{\s*\[native \w/,
	
		// Easily-parseable/retrievable ID or TAG or CLASS selectors
		rquickExpr = /^(?:#([\w-]+)|(\w+)|\.([\w-]+))$/,
	
		rsibling = /[+~]/,
		rescape = /'|\\/g,
	
		// CSS escapes http://www.w3.org/TR/CSS21/syndata.html#escaped-characters
		runescape = new RegExp( "\\\\([\\da-f]{1,6}" + whitespace + "?|(" + whitespace + ")|.)", "ig" ),
		funescape = function( _, escaped, escapedWhitespace ) {
			var high = "0x" + escaped - 0x10000;
			// NaN means non-codepoint
			// Support: Firefox
			// Workaround erroneous numeric interpretation of +"0x"
			return high !== high || escapedWhitespace ?
				escaped :
				high < 0 ?
					// BMP codepoint
					String.fromCharCode( high + 0x10000 ) :
					// Supplemental Plane codepoint (surrogate pair)
					String.fromCharCode( high >> 10 | 0xD800, high & 0x3FF | 0xDC00 );
		};
	
	// Optimize for push.apply( _, NodeList )
	try {
		push.apply(
			(arr = slice.call( preferredDoc.childNodes )),
			preferredDoc.childNodes
		);
		// Support: Android<4.0
		// Detect silently failing push.apply
		arr[ preferredDoc.childNodes.length ].nodeType;
	} catch ( e ) {
		push = { apply: arr.length ?
	
			// Leverage slice if possible
			function( target, els ) {
				push_native.apply( target, slice.call(els) );
			} :
	
			// Support: IE<9
			// Otherwise append directly
			function( target, els ) {
				var j = target.length,
					i = 0;
				// Can't trust NodeList.length
				while ( (target[j++] = els[i++]) ) {}
				target.length = j - 1;
			}
		};
	}
	
	function Sizzle( selector, context, results, seed ) {
		var match, elem, m, nodeType,
			// QSA vars
			i, groups, old, nid, newContext, newSelector;
	
		if ( ( context ? context.ownerDocument || context : preferredDoc ) !== document ) {
			setDocument( context );
		}
	
		context = context || document;
		results = results || [];
	
		if ( !selector || typeof selector !== "string" ) {
			return results;
		}
	
		if ( (nodeType = context.nodeType) !== 1 && nodeType !== 9 ) {
			return [];
		}
		if ( documentIsHTML && !seed ) {
			// Shortcuts
			if ( (match = rquickExpr.exec( selector )) ) {
				// Speed-up: Sizzle("#ID")
				if ( (m = match[1]) ) {
					if ( nodeType === 9 ) {
						elem = context.getElementById( m );
						// Check parentNode to catch when Blackberry 4.6 returns
						// nodes that are no longer in the document (jQuery #6963)
						if ( elem && elem.parentNode ) {
							// Handle the case where IE, Opera, and Webkit return items
							// by name instead of ID
							if ( elem.id === m ) {
								results.push( elem );
								return results;
							}
						} else {
							return results;
						}
					} else {
						// Context is not a document
						if ( context.ownerDocument && (elem = context.ownerDocument.getElementById( m )) &&
							contains( context, elem ) && elem.id === m ) {
							results.push( elem );
							return results;
						}
					}
	
				// Speed-up: Sizzle("TAG")
				} else if ( match[2] ) {
					push.apply( results, context.getElementsByTagName( selector ) );
					return results;
	
				// Speed-up: Sizzle(".CLASS")
				} else if ( (m = match[3]) && support.getElementsByClassName && context.getElementsByClassName ) {
					push.apply( results, context.getElementsByClassName( m ) );
					return results;
				}
			}
	
			// QSA path
			if ( support.qsa && (!rbuggyQSA || !rbuggyQSA.test( selector )) ) {
				nid = old = expando;
				newContext = context;
				newSelector = nodeType === 9 && selector;
	
				// qSA works strangely on Element-rooted queries
				// We can work around this by specifying an extra ID on the root
				// and working up from there (Thanks to Andrew Dupont for the technique)
				// IE 8 doesn't work on object elements
				if ( nodeType === 1 && context.nodeName.toLowerCase() !== "object" ) {
					groups = tokenize( selector );
	
					if ( (old = context.getAttribute("id")) ) {
						nid = old.replace( rescape, "\\$&" );
					} else {
						context.setAttribute( "id", nid );
					}
					nid = "[id='" + nid + "'] ";
	
					i = groups.length;
					while ( i-- ) {
						groups[i] = nid + toSelector( groups[i] );
					}
					newContext = rsibling.test( selector ) && testContext( context.parentNode ) || context;
					newSelector = groups.join(",");
				}
	
				if ( newSelector ) {
					try {
						push.apply( results,
							newContext.querySelectorAll( newSelector )
						);
						return results;
					} catch(qsaError) {
					} finally {
						if ( !old ) {
							context.removeAttribute("id");
						}
					}
				}
			}
		}
	
		// All others
		return select( selector.replace( rtrim, "$1" ), context, results, seed );
	}
	
	/**
	 * Create key-value caches of limited size
	 * @returns {Function(string, Object)} Returns the Object data after storing it on itself with
	 *	property name the (space-suffixed) string and (if the cache is larger than Expr.cacheLength)
	 *	deleting the oldest entry
	 */
	function createCache() {
		var keys = [];
	
		function cache( key, value ) {
			// Use (key + " ") to avoid collision with native prototype properties (see Issue #157)
			if ( keys.push( key + " " ) > Expr.cacheLength ) {
				// Only keep the most recent entries
				delete cache[ keys.shift() ];
			}
			return (cache[ key + " " ] = value);
		}
		return cache;
	}
	
	/**
	 * Mark a function for special use by Sizzle
	 * @param {Function} fn The function to mark
	 */
	function markFunction( fn ) {
		fn[ expando ] = true;
		return fn;
	}
	
	/**
	 * Support testing using an element
	 * @param {Function} fn Passed the created div and expects a boolean result
	 */
	function assert( fn ) {
		var div = document.createElement("div");
	
		try {
			return !!fn( div );
		} catch (e) {
			return false;
		} finally {
			// Remove from its parent by default
			if ( div.parentNode ) {
				div.parentNode.removeChild( div );
			}
			// release memory in IE
			div = null;
		}
	}
	
	/**
	 * Adds the same handler for all of the specified attrs
	 * @param {String} attrs Pipe-separated list of attributes
	 * @param {Function} handler The method that will be applied
	 */
	function addHandle( attrs, handler ) {
		var arr = attrs.split("|"),
			i = attrs.length;
	
		while ( i-- ) {
			Expr.attrHandle[ arr[i] ] = handler;
		}
	}
	
	/**
	 * Checks document order of two siblings
	 * @param {Element} a
	 * @param {Element} b
	 * @returns {Number} Returns less than 0 if a precedes b, greater than 0 if a follows b
	 */
	function siblingCheck( a, b ) {
		var cur = b && a,
			diff = cur && a.nodeType === 1 && b.nodeType === 1 &&
				( ~b.sourceIndex || MAX_NEGATIVE ) -
				( ~a.sourceIndex || MAX_NEGATIVE );
	
		// Use IE sourceIndex if available on both nodes
		if ( diff ) {
			return diff;
		}
	
		// Check if b follows a
		if ( cur ) {
			while ( (cur = cur.nextSibling) ) {
				if ( cur === b ) {
					return -1;
				}
			}
		}
	
		return a ? 1 : -1;
	}
	
	/**
	 * Returns a function to use in pseudos for input types
	 * @param {String} type
	 */
	function createInputPseudo( type ) {
		return function( elem ) {
			var name = elem.nodeName.toLowerCase();
			return name === "input" && elem.type === type;
		};
	}
	
	/**
	 * Returns a function to use in pseudos for buttons
	 * @param {String} type
	 */
	function createButtonPseudo( type ) {
		return function( elem ) {
			var name = elem.nodeName.toLowerCase();
			return (name === "input" || name === "button") && elem.type === type;
		};
	}
	
	/**
	 * Returns a function to use in pseudos for positionals
	 * @param {Function} fn
	 */
	function createPositionalPseudo( fn ) {
		return markFunction(function( argument ) {
			argument = +argument;
			return markFunction(function( seed, matches ) {
				var j,
					matchIndexes = fn( [], seed.length, argument ),
					i = matchIndexes.length;
	
				// Match elements found at the specified indexes
				while ( i-- ) {
					if ( seed[ (j = matchIndexes[i]) ] ) {
						seed[j] = !(matches[j] = seed[j]);
					}
				}
			});
		});
	}
	
	/**
	 * Checks a node for validity as a Sizzle context
	 * @param {Element|Object=} context
	 * @returns {Element|Object|Boolean} The input node if acceptable, otherwise a falsy value
	 */
	function testContext( context ) {
		return context && typeof context.getElementsByTagName !== strundefined && context;
	}
	
	// Expose support vars for convenience
	support = Sizzle.support = {};
	
	/**
	 * Detects XML nodes
	 * @param {Element|Object} elem An element or a document
	 * @returns {Boolean} True iff elem is a non-HTML XML node
	 */
	isXML = Sizzle.isXML = function( elem ) {
		// documentElement is verified for cases where it doesn't yet exist
		// (such as loading iframes in IE - #4833)
		var documentElement = elem && (elem.ownerDocument || elem).documentElement;
		return documentElement ? documentElement.nodeName !== "HTML" : false;
	};
	
	/**
	 * Sets document-related variables once based on the current document
	 * @param {Element|Object} [doc] An element or document object to use to set the document
	 * @returns {Object} Returns the current document
	 */
	setDocument = Sizzle.setDocument = function( node ) {
		var doc = node ? node.ownerDocument || node : preferredDoc,
			parent = doc.defaultView;
	
		// If no document and documentElement is available, return
		if ( doc === document || doc.nodeType !== 9 || !doc.documentElement ) {
			return document;
		}
	
		// Set our document
		document = doc;
		docElem = doc.documentElement;
	
		// Support tests
		documentIsHTML = !isXML( doc );
	
		// Support: IE>8
		// If iframe document is assigned to "document" variable and if iframe has been reloaded,
		// IE will throw "permission denied" error when accessing "document" variable, see jQuery #13936
		// IE6-8 do not support the defaultView property so parent will be undefined
		if ( parent && parent.attachEvent && parent !== parent.top ) {
			parent.attachEvent( "onbeforeunload", function() {
				setDocument();
			});
		}
	
		/* Attributes
		---------------------------------------------------------------------- */
	
		// Support: IE<8
		// Verify that getAttribute really returns attributes and not properties (excepting IE8 booleans)
		support.attributes = assert(function( div ) {
			div.className = "i";
			return !div.getAttribute("className");
		});
	
		/* getElement(s)By*
		---------------------------------------------------------------------- */
	
		// Check if getElementsByTagName("*") returns only elements
		support.getElementsByTagName = assert(function( div ) {
			div.appendChild( doc.createComment("") );
			return !div.getElementsByTagName("*").length;
		});
	
		// Check if getElementsByClassName can be trusted
		support.getElementsByClassName = assert(function( div ) {
			div.innerHTML = "<div class='a'></div><div class='a i'></div>";
	
			// Support: Safari<4
			// Catch class over-caching
			div.firstChild.className = "i";
			// Support: Opera<10
			// Catch gEBCN failure to find non-leading classes
			return div.getElementsByClassName("i").length === 2;
		});
	
		// Support: IE<10
		// Check if getElementById returns elements by name
		// The broken getElementById methods don't pick up programatically-set names,
		// so use a roundabout getElementsByName test
		support.getById = assert(function( div ) {
			docElem.appendChild( div ).id = expando;
			return !doc.getElementsByName || !doc.getElementsByName( expando ).length;
		});
	
		// ID find and filter
		if ( support.getById ) {
			Expr.find["ID"] = function( id, context ) {
				if ( typeof context.getElementById !== strundefined && documentIsHTML ) {
					var m = context.getElementById( id );
					// Check parentNode to catch when Blackberry 4.6 returns
					// nodes that are no longer in the document #6963
					return m && m.parentNode ? [m] : [];
				}
			};
			Expr.filter["ID"] = function( id ) {
				var attrId = id.replace( runescape, funescape );
				return function( elem ) {
					return elem.getAttribute("id") === attrId;
				};
			};
		} else {
			// Support: IE6/7
			// getElementById is not reliable as a find shortcut
			delete Expr.find["ID"];
	
			Expr.filter["ID"] =  function( id ) {
				var attrId = id.replace( runescape, funescape );
				return function( elem ) {
					var node = typeof elem.getAttributeNode !== strundefined && elem.getAttributeNode("id");
					return node && node.value === attrId;
				};
			};
		}
	
		// Tag
		Expr.find["TAG"] = support.getElementsByTagName ?
			function( tag, context ) {
				if ( typeof context.getElementsByTagName !== strundefined ) {
					return context.getElementsByTagName( tag );
				}
			} :
			function( tag, context ) {
				var elem,
					tmp = [],
					i = 0,
					results = context.getElementsByTagName( tag );
	
				// Filter out possible comments
				if ( tag === "*" ) {
					while ( (elem = results[i++]) ) {
						if ( elem.nodeType === 1 ) {
							tmp.push( elem );
						}
					}
	
					return tmp;
				}
				return results;
			};
	
		// Class
		Expr.find["CLASS"] = support.getElementsByClassName && function( className, context ) {
			if ( typeof context.getElementsByClassName !== strundefined && documentIsHTML ) {
				return context.getElementsByClassName( className );
			}
		};
	
		/* QSA/matchesSelector
		---------------------------------------------------------------------- */
	
		// QSA and matchesSelector support
	
		// matchesSelector(:active) reports false when true (IE9/Opera 11.5)
		rbuggyMatches = [];
	
		// qSa(:focus) reports false when true (Chrome 21)
		// We allow this because of a bug in IE8/9 that throws an error
		// whenever `document.activeElement` is accessed on an iframe
		// So, we allow :focus to pass through QSA all the time to avoid the IE error
		// See http://bugs.jquery.com/ticket/13378
		rbuggyQSA = [];
	
		if ( (support.qsa = rnative.test( doc.querySelectorAll )) ) {
			// Build QSA regex
			// Regex strategy adopted from Diego Perini
			assert(function( div ) {
				// Select is set to empty string on purpose
				// This is to test IE's treatment of not explicitly
				// setting a boolean content attribute,
				// since its presence should be enough
				// http://bugs.jquery.com/ticket/12359
				div.innerHTML = "<select><option selected=''></option></select>";
	
				// Support: IE8
				// Boolean attributes and "value" are not treated correctly
				if ( !div.querySelectorAll("[selected]").length ) {
					rbuggyQSA.push( "\\[" + whitespace + "*(?:value|" + booleans + ")" );
				}
	
				// Webkit/Opera - :checked should return selected option elements
				// http://www.w3.org/TR/2011/REC-css3-selectors-20110929/#checked
				// IE8 throws error here and will not see later tests
				if ( !div.querySelectorAll(":checked").length ) {
					rbuggyQSA.push(":checked");
				}
			});
	
			assert(function( div ) {
	
				// Support: Opera 10-12/IE8
				// ^= $= *= and empty values
				// Should not select anything
				// Support: Windows 8 Native Apps
				// The type attribute is restricted during .innerHTML assignment
				var input = doc.createElement("input");
				input.setAttribute( "type", "hidden" );
				div.appendChild( input ).setAttribute( "t", "" );
	
				if ( div.querySelectorAll("[t^='']").length ) {
					rbuggyQSA.push( "[*^$]=" + whitespace + "*(?:''|\"\")" );
				}
	
				// FF 3.5 - :enabled/:disabled and hidden elements (hidden elements are still enabled)
				// IE8 throws error here and will not see later tests
				if ( !div.querySelectorAll(":enabled").length ) {
					rbuggyQSA.push( ":enabled", ":disabled" );
				}
	
				// Opera 10-11 does not throw on post-comma invalid pseudos
				div.querySelectorAll("*,:x");
				rbuggyQSA.push(",.*:");
			});
		}
	
		if ( (support.matchesSelector = rnative.test( (matches = docElem.webkitMatchesSelector ||
			docElem.mozMatchesSelector ||
			docElem.oMatchesSelector ||
			docElem.msMatchesSelector) )) ) {
	
			assert(function( div ) {
				// Check to see if it's possible to do matchesSelector
				// on a disconnected node (IE 9)
				support.disconnectedMatch = matches.call( div, "div" );
	
				// This should fail with an exception
				// Gecko does not error, returns false instead
				matches.call( div, "[s!='']:x" );
				rbuggyMatches.push( "!=", pseudos );
			});
		}
	
		rbuggyQSA = rbuggyQSA.length && new RegExp( rbuggyQSA.join("|") );
		rbuggyMatches = rbuggyMatches.length && new RegExp( rbuggyMatches.join("|") );
	
		/* Contains
		---------------------------------------------------------------------- */
	
		// Element contains another
		// Purposefully does not implement inclusive descendent
		// As in, an element does not contain itself
		contains = rnative.test( docElem.contains ) || docElem.compareDocumentPosition ?
			function( a, b ) {
				var adown = a.nodeType === 9 ? a.documentElement : a,
					bup = b && b.parentNode;
				return a === bup || !!( bup && bup.nodeType === 1 && (
					adown.contains ?
						adown.contains( bup ) :
						a.compareDocumentPosition && a.compareDocumentPosition( bup ) & 16
				));
			} :
			function( a, b ) {
				if ( b ) {
					while ( (b = b.parentNode) ) {
						if ( b === a ) {
							return true;
						}
					}
				}
				return false;
			};
	
		/* Sorting
		---------------------------------------------------------------------- */
	
		// Document order sorting
		sortOrder = docElem.compareDocumentPosition ?
		function( a, b ) {
	
			// Flag for duplicate removal
			if ( a === b ) {
				hasDuplicate = true;
				return 0;
			}
	
			var compare = b.compareDocumentPosition && a.compareDocumentPosition && a.compareDocumentPosition( b );
	
			if ( compare ) {
				// Disconnected nodes
				if ( compare & 1 ||
					(!support.sortDetached && b.compareDocumentPosition( a ) === compare) ) {
	
					// Choose the first element that is related to our preferred document
					if ( a === doc || contains(preferredDoc, a) ) {
						return -1;
					}
					if ( b === doc || contains(preferredDoc, b) ) {
						return 1;
					}
	
					// Maintain original order
					return sortInput ?
						( indexOf.call( sortInput, a ) - indexOf.call( sortInput, b ) ) :
						0;
				}
	
				return compare & 4 ? -1 : 1;
			}
	
			// Not directly comparable, sort on existence of method
			return a.compareDocumentPosition ? -1 : 1;
		} :
		function( a, b ) {
			var cur,
				i = 0,
				aup = a.parentNode,
				bup = b.parentNode,
				ap = [ a ],
				bp = [ b ];
	
			// Exit early if the nodes are identical
			if ( a === b ) {
				hasDuplicate = true;
				return 0;
	
			// Parentless nodes are either documents or disconnected
			} else if ( !aup || !bup ) {
				return a === doc ? -1 :
					b === doc ? 1 :
					aup ? -1 :
					bup ? 1 :
					sortInput ?
					( indexOf.call( sortInput, a ) - indexOf.call( sortInput, b ) ) :
					0;
	
			// If the nodes are siblings, we can do a quick check
			} else if ( aup === bup ) {
				return siblingCheck( a, b );
			}
	
			// Otherwise we need full lists of their ancestors for comparison
			cur = a;
			while ( (cur = cur.parentNode) ) {
				ap.unshift( cur );
			}
			cur = b;
			while ( (cur = cur.parentNode) ) {
				bp.unshift( cur );
			}
	
			// Walk down the tree looking for a discrepancy
			while ( ap[i] === bp[i] ) {
				i++;
			}
	
			return i ?
				// Do a sibling check if the nodes have a common ancestor
				siblingCheck( ap[i], bp[i] ) :
	
				// Otherwise nodes in our document sort first
				ap[i] === preferredDoc ? -1 :
				bp[i] === preferredDoc ? 1 :
				0;
		};
	
		return doc;
	};
	
	Sizzle.matches = function( expr, elements ) {
		return Sizzle( expr, null, null, elements );
	};
	
	Sizzle.matchesSelector = function( elem, expr ) {
		// Set document vars if needed
		if ( ( elem.ownerDocument || elem ) !== document ) {
			setDocument( elem );
		}
	
		// Make sure that attribute selectors are quoted
		expr = expr.replace( rattributeQuotes, "='$1']" );
	
		if ( support.matchesSelector && documentIsHTML &&
			( !rbuggyMatches || !rbuggyMatches.test( expr ) ) &&
			( !rbuggyQSA     || !rbuggyQSA.test( expr ) ) ) {
	
			try {
				var ret = matches.call( elem, expr );
	
				// IE 9's matchesSelector returns false on disconnected nodes
				if ( ret || support.disconnectedMatch ||
						// As well, disconnected nodes are said to be in a document
						// fragment in IE 9
						elem.document && elem.document.nodeType !== 11 ) {
					return ret;
				}
			} catch(e) {}
		}
	
		return Sizzle( expr, document, null, [elem] ).length > 0;
	};
	
	Sizzle.contains = function( context, elem ) {
		// Set document vars if needed
		if ( ( context.ownerDocument || context ) !== document ) {
			setDocument( context );
		}
		return contains( context, elem );
	};
	
	Sizzle.attr = function( elem, name ) {
		// Set document vars if needed
		if ( ( elem.ownerDocument || elem ) !== document ) {
			setDocument( elem );
		}
	
		var fn = Expr.attrHandle[ name.toLowerCase() ],
			// Don't get fooled by Object.prototype properties (jQuery #13807)
			val = fn && hasOwn.call( Expr.attrHandle, name.toLowerCase() ) ?
				fn( elem, name, !documentIsHTML ) :
				undefined;
	
		return val !== undefined ?
			val :
			support.attributes || !documentIsHTML ?
				elem.getAttribute( name ) :
				(val = elem.getAttributeNode(name)) && val.specified ?
					val.value :
					null;
	};
	
	Sizzle.error = function( msg ) {
		throw new Error( "Syntax error, unrecognized expression: " + msg );
	};
	
	/**
	 * Document sorting and removing duplicates
	 * @param {ArrayLike} results
	 */
	Sizzle.uniqueSort = function( results ) {
		var elem,
			duplicates = [],
			j = 0,
			i = 0;
	
		// Unless we *know* we can detect duplicates, assume their presence
		hasDuplicate = !support.detectDuplicates;
		sortInput = !support.sortStable && results.slice( 0 );
		results.sort( sortOrder );
	
		if ( hasDuplicate ) {
			while ( (elem = results[i++]) ) {
				if ( elem === results[ i ] ) {
					j = duplicates.push( i );
				}
			}
			while ( j-- ) {
				results.splice( duplicates[ j ], 1 );
			}
		}
	
		return results;
	};
	
	/**
	 * Utility function for retrieving the text value of an array of DOM nodes
	 * @param {Array|Element} elem
	 */
	getText = Sizzle.getText = function( elem ) {
		var node,
			ret = "",
			i = 0,
			nodeType = elem.nodeType;
	
		if ( !nodeType ) {
			// If no nodeType, this is expected to be an array
			while ( (node = elem[i++]) ) {
				// Do not traverse comment nodes
				ret += getText( node );
			}
		} else if ( nodeType === 1 || nodeType === 9 || nodeType === 11 ) {
			// Use textContent for elements
			// innerText usage removed for consistency of new lines (jQuery #11153)
			if ( typeof elem.textContent === "string" ) {
				return elem.textContent;
			} else {
				// Traverse its children
				for ( elem = elem.firstChild; elem; elem = elem.nextSibling ) {
					ret += getText( elem );
				}
			}
		} else if ( nodeType === 3 || nodeType === 4 ) {
			return elem.nodeValue;
		}
		// Do not include comment or processing instruction nodes
	
		return ret;
	};
	
	Expr = Sizzle.selectors = {
	
		// Can be adjusted by the user
		cacheLength: 50,
	
		createPseudo: markFunction,
	
		match: matchExpr,
	
		attrHandle: {},
	
		find: {},
	
		relative: {
			">": { dir: "parentNode", first: true },
			" ": { dir: "parentNode" },
			"+": { dir: "previousSibling", first: true },
			"~": { dir: "previousSibling" }
		},
	
		preFilter: {
			"ATTR": function( match ) {
				match[1] = match[1].replace( runescape, funescape );
	
				// Move the given value to match[3] whether quoted or unquoted
				match[3] = ( match[4] || match[5] || "" ).replace( runescape, funescape );
	
				if ( match[2] === "~=" ) {
					match[3] = " " + match[3] + " ";
				}
	
				return match.slice( 0, 4 );
			},
	
			"CHILD": function( match ) {
				/* matches from matchExpr["CHILD"]
					1 type (only|nth|...)
					2 what (child|of-type)
					3 argument (even|odd|\d*|\d*n([+-]\d+)?|...)
					4 xn-component of xn+y argument ([+-]?\d*n|)
					5 sign of xn-component
					6 x of xn-component
					7 sign of y-component
					8 y of y-component
				*/
				match[1] = match[1].toLowerCase();
	
				if ( match[1].slice( 0, 3 ) === "nth" ) {
					// nth-* requires argument
					if ( !match[3] ) {
						Sizzle.error( match[0] );
					}
	
					// numeric x and y parameters for Expr.filter.CHILD
					// remember that false/true cast respectively to 0/1
					match[4] = +( match[4] ? match[5] + (match[6] || 1) : 2 * ( match[3] === "even" || match[3] === "odd" ) );
					match[5] = +( ( match[7] + match[8] ) || match[3] === "odd" );
	
				// other types prohibit arguments
				} else if ( match[3] ) {
					Sizzle.error( match[0] );
				}
	
				return match;
			},
	
			"PSEUDO": function( match ) {
				var excess,
					unquoted = !match[5] && match[2];
	
				if ( matchExpr["CHILD"].test( match[0] ) ) {
					return null;
				}
	
				// Accept quoted arguments as-is
				if ( match[3] && match[4] !== undefined ) {
					match[2] = match[4];
	
				// Strip excess characters from unquoted arguments
				} else if ( unquoted && rpseudo.test( unquoted ) &&
					// Get excess from tokenize (recursively)
					(excess = tokenize( unquoted, true )) &&
					// advance to the next closing parenthesis
					(excess = unquoted.indexOf( ")", unquoted.length - excess ) - unquoted.length) ) {
	
					// excess is a negative index
					match[0] = match[0].slice( 0, excess );
					match[2] = unquoted.slice( 0, excess );
				}
	
				// Return only captures needed by the pseudo filter method (type and argument)
				return match.slice( 0, 3 );
			}
		},
	
		filter: {
	
			"TAG": function( nodeNameSelector ) {
				var nodeName = nodeNameSelector.replace( runescape, funescape ).toLowerCase();
				return nodeNameSelector === "*" ?
					function() { return true; } :
					function( elem ) {
						return elem.nodeName && elem.nodeName.toLowerCase() === nodeName;
					};
			},
	
			"CLASS": function( className ) {
				var pattern = classCache[ className + " " ];
	
				return pattern ||
					(pattern = new RegExp( "(^|" + whitespace + ")" + className + "(" + whitespace + "|$)" )) &&
					classCache( className, function( elem ) {
						return pattern.test( typeof elem.className === "string" && elem.className || typeof elem.getAttribute !== strundefined && elem.getAttribute("class") || "" );
					});
			},
	
			"ATTR": function( name, operator, check ) {
				return function( elem ) {
					var result = Sizzle.attr( elem, name );
	
					if ( result == null ) {
						return operator === "!=";
					}
					if ( !operator ) {
						return true;
					}
	
					result += "";
	
					return operator === "=" ? result === check :
						operator === "!=" ? result !== check :
						operator === "^=" ? check && result.indexOf( check ) === 0 :
						operator === "*=" ? check && result.indexOf( check ) > -1 :
						operator === "$=" ? check && result.slice( -check.length ) === check :
						operator === "~=" ? ( " " + result + " " ).indexOf( check ) > -1 :
						operator === "|=" ? result === check || result.slice( 0, check.length + 1 ) === check + "-" :
						false;
				};
			},
	
			"CHILD": function( type, what, argument, first, last ) {
				var simple = type.slice( 0, 3 ) !== "nth",
					forward = type.slice( -4 ) !== "last",
					ofType = what === "of-type";
	
				return first === 1 && last === 0 ?
	
					// Shortcut for :nth-*(n)
					function( elem ) {
						return !!elem.parentNode;
					} :
	
					function( elem, context, xml ) {
						var cache, outerCache, node, diff, nodeIndex, start,
							dir = simple !== forward ? "nextSibling" : "previousSibling",
							parent = elem.parentNode,
							name = ofType && elem.nodeName.toLowerCase(),
							useCache = !xml && !ofType;
	
						if ( parent ) {
	
							// :(first|last|only)-(child|of-type)
							if ( simple ) {
								while ( dir ) {
									node = elem;
									while ( (node = node[ dir ]) ) {
										if ( ofType ? node.nodeName.toLowerCase() === name : node.nodeType === 1 ) {
											return false;
										}
									}
									// Reverse direction for :only-* (if we haven't yet done so)
									start = dir = type === "only" && !start && "nextSibling";
								}
								return true;
							}
	
							start = [ forward ? parent.firstChild : parent.lastChild ];
	
							// non-xml :nth-child(...) stores cache data on `parent`
							if ( forward && useCache ) {
								// Seek `elem` from a previously-cached index
								outerCache = parent[ expando ] || (parent[ expando ] = {});
								cache = outerCache[ type ] || [];
								nodeIndex = cache[0] === dirruns && cache[1];
								diff = cache[0] === dirruns && cache[2];
								node = nodeIndex && parent.childNodes[ nodeIndex ];
	
								while ( (node = ++nodeIndex && node && node[ dir ] ||
	
									// Fallback to seeking `elem` from the start
									(diff = nodeIndex = 0) || start.pop()) ) {
	
									// When found, cache indexes on `parent` and break
									if ( node.nodeType === 1 && ++diff && node === elem ) {
										outerCache[ type ] = [ dirruns, nodeIndex, diff ];
										break;
									}
								}
	
							// Use previously-cached element index if available
							} else if ( useCache && (cache = (elem[ expando ] || (elem[ expando ] = {}))[ type ]) && cache[0] === dirruns ) {
								diff = cache[1];
	
							// xml :nth-child(...) or :nth-last-child(...) or :nth(-last)?-of-type(...)
							} else {
								// Use the same loop as above to seek `elem` from the start
								while ( (node = ++nodeIndex && node && node[ dir ] ||
									(diff = nodeIndex = 0) || start.pop()) ) {
	
									if ( ( ofType ? node.nodeName.toLowerCase() === name : node.nodeType === 1 ) && ++diff ) {
										// Cache the index of each encountered element
										if ( useCache ) {
											(node[ expando ] || (node[ expando ] = {}))[ type ] = [ dirruns, diff ];
										}
	
										if ( node === elem ) {
											break;
										}
									}
								}
							}
	
							// Incorporate the offset, then check against cycle size
							diff -= last;
							return diff === first || ( diff % first === 0 && diff / first >= 0 );
						}
					};
			},
	
			"PSEUDO": function( pseudo, argument ) {
				// pseudo-class names are case-insensitive
				// http://www.w3.org/TR/selectors/#pseudo-classes
				// Prioritize by case sensitivity in case custom pseudos are added with uppercase letters
				// Remember that setFilters inherits from pseudos
				var args,
					fn = Expr.pseudos[ pseudo ] || Expr.setFilters[ pseudo.toLowerCase() ] ||
						Sizzle.error( "unsupported pseudo: " + pseudo );
	
				// The user may use createPseudo to indicate that
				// arguments are needed to create the filter function
				// just as Sizzle does
				if ( fn[ expando ] ) {
					return fn( argument );
				}
	
				// But maintain support for old signatures
				if ( fn.length > 1 ) {
					args = [ pseudo, pseudo, "", argument ];
					return Expr.setFilters.hasOwnProperty( pseudo.toLowerCase() ) ?
						markFunction(function( seed, matches ) {
							var idx,
								matched = fn( seed, argument ),
								i = matched.length;
							while ( i-- ) {
								idx = indexOf.call( seed, matched[i] );
								seed[ idx ] = !( matches[ idx ] = matched[i] );
							}
						}) :
						function( elem ) {
							return fn( elem, 0, args );
						};
				}
	
				return fn;
			}
		},
	
		pseudos: {
			// Potentially complex pseudos
			"not": markFunction(function( selector ) {
				// Trim the selector passed to compile
				// to avoid treating leading and trailing
				// spaces as combinators
				var input = [],
					results = [],
					matcher = compile( selector.replace( rtrim, "$1" ) );
	
				return matcher[ expando ] ?
					markFunction(function( seed, matches, context, xml ) {
						var elem,
							unmatched = matcher( seed, null, xml, [] ),
							i = seed.length;
	
						// Match elements unmatched by `matcher`
						while ( i-- ) {
							if ( (elem = unmatched[i]) ) {
								seed[i] = !(matches[i] = elem);
							}
						}
					}) :
					function( elem, context, xml ) {
						input[0] = elem;
						matcher( input, null, xml, results );
						return !results.pop();
					};
			}),
	
			"has": markFunction(function( selector ) {
				return function( elem ) {
					return Sizzle( selector, elem ).length > 0;
				};
			}),
	
			"contains": markFunction(function( text ) {
				return function( elem ) {
					return ( elem.textContent || elem.innerText || getText( elem ) ).indexOf( text ) > -1;
				};
			}),
	
			// "Whether an element is represented by a :lang() selector
			// is based solely on the element's language value
			// being equal to the identifier C,
			// or beginning with the identifier C immediately followed by "-".
			// The matching of C against the element's language value is performed case-insensitively.
			// The identifier C does not have to be a valid language name."
			// http://www.w3.org/TR/selectors/#lang-pseudo
			"lang": markFunction( function( lang ) {
				// lang value must be a valid identifier
				if ( !ridentifier.test(lang || "") ) {
					Sizzle.error( "unsupported lang: " + lang );
				}
				lang = lang.replace( runescape, funescape ).toLowerCase();
				return function( elem ) {
					var elemLang;
					do {
						if ( (elemLang = documentIsHTML ?
							elem.lang :
							elem.getAttribute("xml:lang") || elem.getAttribute("lang")) ) {
	
							elemLang = elemLang.toLowerCase();
							return elemLang === lang || elemLang.indexOf( lang + "-" ) === 0;
						}
					} while ( (elem = elem.parentNode) && elem.nodeType === 1 );
					return false;
				};
			}),
	
			// Miscellaneous
			"target": function( elem ) {
				var hash = window.location && window.location.hash;
				return hash && hash.slice( 1 ) === elem.id;
			},
	
			"root": function( elem ) {
				return elem === docElem;
			},
	
			"focus": function( elem ) {
				return elem === document.activeElement && (!document.hasFocus || document.hasFocus()) && !!(elem.type || elem.href || ~elem.tabIndex);
			},
	
			// Boolean properties
			"enabled": function( elem ) {
				return elem.disabled === false;
			},
	
			"disabled": function( elem ) {
				return elem.disabled === true;
			},
	
			"checked": function( elem ) {
				// In CSS3, :checked should return both checked and selected elements
				// http://www.w3.org/TR/2011/REC-css3-selectors-20110929/#checked
				var nodeName = elem.nodeName.toLowerCase();
				return (nodeName === "input" && !!elem.checked) || (nodeName === "option" && !!elem.selected);
			},
	
			"selected": function( elem ) {
				// Accessing this property makes selected-by-default
				// options in Safari work properly
				if ( elem.parentNode ) {
					elem.parentNode.selectedIndex;
				}
	
				return elem.selected === true;
			},
	
			// Contents
			"empty": function( elem ) {
				// http://www.w3.org/TR/selectors/#empty-pseudo
				// :empty is negated by element (1) or content nodes (text: 3; cdata: 4; entity ref: 5),
				//   but not by others (comment: 8; processing instruction: 7; etc.)
				// nodeType < 6 works because attributes (2) do not appear as children
				for ( elem = elem.firstChild; elem; elem = elem.nextSibling ) {
					if ( elem.nodeType < 6 ) {
						return false;
					}
				}
				return true;
			},
	
			"parent": function( elem ) {
				return !Expr.pseudos["empty"]( elem );
			},
	
			// Element/input types
			"header": function( elem ) {
				return rheader.test( elem.nodeName );
			},
	
			"input": function( elem ) {
				return rinputs.test( elem.nodeName );
			},
	
			"button": function( elem ) {
				var name = elem.nodeName.toLowerCase();
				return name === "input" && elem.type === "button" || name === "button";
			},
	
			"text": function( elem ) {
				var attr;
				return elem.nodeName.toLowerCase() === "input" &&
					elem.type === "text" &&
	
					// Support: IE<8
					// New HTML5 attribute values (e.g., "search") appear with elem.type === "text"
					( (attr = elem.getAttribute("type")) == null || attr.toLowerCase() === elem.type );
			},
	
			// Position-in-collection
			"first": createPositionalPseudo(function() {
				return [ 0 ];
			}),
	
			"last": createPositionalPseudo(function( matchIndexes, length ) {
				return [ length - 1 ];
			}),
	
			"eq": createPositionalPseudo(function( matchIndexes, length, argument ) {
				return [ argument < 0 ? argument + length : argument ];
			}),
	
			"even": createPositionalPseudo(function( matchIndexes, length ) {
				var i = 0;
				for ( ; i < length; i += 2 ) {
					matchIndexes.push( i );
				}
				return matchIndexes;
			}),
	
			"odd": createPositionalPseudo(function( matchIndexes, length ) {
				var i = 1;
				for ( ; i < length; i += 2 ) {
					matchIndexes.push( i );
				}
				return matchIndexes;
			}),
	
			"lt": createPositionalPseudo(function( matchIndexes, length, argument ) {
				var i = argument < 0 ? argument + length : argument;
				for ( ; --i >= 0; ) {
					matchIndexes.push( i );
				}
				return matchIndexes;
			}),
	
			"gt": createPositionalPseudo(function( matchIndexes, length, argument ) {
				var i = argument < 0 ? argument + length : argument;
				for ( ; ++i < length; ) {
					matchIndexes.push( i );
				}
				return matchIndexes;
			})
		}
	};
	
	Expr.pseudos["nth"] = Expr.pseudos["eq"];
	
	// Add button/input type pseudos
	for ( i in { radio: true, checkbox: true, file: true, password: true, image: true } ) {
		Expr.pseudos[ i ] = createInputPseudo( i );
	}
	for ( i in { submit: true, reset: true } ) {
		Expr.pseudos[ i ] = createButtonPseudo( i );
	}
	
	// Easy API for creating new setFilters
	function setFilters() {}
	setFilters.prototype = Expr.filters = Expr.pseudos;
	Expr.setFilters = new setFilters();
	
	function tokenize( selector, parseOnly ) {
		var matched, match, tokens, type,
			soFar, groups, preFilters,
			cached = tokenCache[ selector + " " ];
	
		if ( cached ) {
			return parseOnly ? 0 : cached.slice( 0 );
		}
	
		soFar = selector;
		groups = [];
		preFilters = Expr.preFilter;
	
		while ( soFar ) {
	
			// Comma and first run
			if ( !matched || (match = rcomma.exec( soFar )) ) {
				if ( match ) {
					// Don't consume trailing commas as valid
					soFar = soFar.slice( match[0].length ) || soFar;
				}
				groups.push( (tokens = []) );
			}
	
			matched = false;
	
			// Combinators
			if ( (match = rcombinators.exec( soFar )) ) {
				matched = match.shift();
				tokens.push({
					value: matched,
					// Cast descendant combinators to space
					type: match[0].replace( rtrim, " " )
				});
				soFar = soFar.slice( matched.length );
			}
	
			// Filters
			for ( type in Expr.filter ) {
				if ( (match = matchExpr[ type ].exec( soFar )) && (!preFilters[ type ] ||
					(match = preFilters[ type ]( match ))) ) {
					matched = match.shift();
					tokens.push({
						value: matched,
						type: type,
						matches: match
					});
					soFar = soFar.slice( matched.length );
				}
			}
	
			if ( !matched ) {
				break;
			}
		}
	
		// Return the length of the invalid excess
		// if we're just parsing
		// Otherwise, throw an error or return tokens
		return parseOnly ?
			soFar.length :
			soFar ?
				Sizzle.error( selector ) :
				// Cache the tokens
				tokenCache( selector, groups ).slice( 0 );
	}
	
	function toSelector( tokens ) {
		var i = 0,
			len = tokens.length,
			selector = "";
		for ( ; i < len; i++ ) {
			selector += tokens[i].value;
		}
		return selector;
	}
	
	function addCombinator( matcher, combinator, base ) {
		var dir = combinator.dir,
			checkNonElements = base && dir === "parentNode",
			doneName = done++;
	
		return combinator.first ?
			// Check against closest ancestor/preceding element
			function( elem, context, xml ) {
				while ( (elem = elem[ dir ]) ) {
					if ( elem.nodeType === 1 || checkNonElements ) {
						return matcher( elem, context, xml );
					}
				}
			} :
	
			// Check against all ancestor/preceding elements
			function( elem, context, xml ) {
				var data, cache, outerCache,
					dirkey = dirruns + " " + doneName;
	
				// We can't set arbitrary data on XML nodes, so they don't benefit from dir caching
				if ( xml ) {
					while ( (elem = elem[ dir ]) ) {
						if ( elem.nodeType === 1 || checkNonElements ) {
							if ( matcher( elem, context, xml ) ) {
								return true;
							}
						}
					}
				} else {
					while ( (elem = elem[ dir ]) ) {
						if ( elem.nodeType === 1 || checkNonElements ) {
							outerCache = elem[ expando ] || (elem[ expando ] = {});
							if ( (cache = outerCache[ dir ]) && cache[0] === dirkey ) {
								if ( (data = cache[1]) === true || data === cachedruns ) {
									return data === true;
								}
							} else {
								cache = outerCache[ dir ] = [ dirkey ];
								cache[1] = matcher( elem, context, xml ) || cachedruns;
								if ( cache[1] === true ) {
									return true;
								}
							}
						}
					}
				}
			};
	}
	
	function elementMatcher( matchers ) {
		return matchers.length > 1 ?
			function( elem, context, xml ) {
				var i = matchers.length;
				while ( i-- ) {
					if ( !matchers[i]( elem, context, xml ) ) {
						return false;
					}
				}
				return true;
			} :
			matchers[0];
	}
	
	function condense( unmatched, map, filter, context, xml ) {
		var elem,
			newUnmatched = [],
			i = 0,
			len = unmatched.length,
			mapped = map != null;
	
		for ( ; i < len; i++ ) {
			if ( (elem = unmatched[i]) ) {
				if ( !filter || filter( elem, context, xml ) ) {
					newUnmatched.push( elem );
					if ( mapped ) {
						map.push( i );
					}
				}
			}
		}
	
		return newUnmatched;
	}
	
	function setMatcher( preFilter, selector, matcher, postFilter, postFinder, postSelector ) {
		if ( postFilter && !postFilter[ expando ] ) {
			postFilter = setMatcher( postFilter );
		}
		if ( postFinder && !postFinder[ expando ] ) {
			postFinder = setMatcher( postFinder, postSelector );
		}
		return markFunction(function( seed, results, context, xml ) {
			var temp, i, elem,
				preMap = [],
				postMap = [],
				preexisting = results.length,
	
				// Get initial elements from seed or context
				elems = seed || multipleContexts( selector || "*", context.nodeType ? [ context ] : context, [] ),
	
				// Prefilter to get matcher input, preserving a map for seed-results synchronization
				matcherIn = preFilter && ( seed || !selector ) ?
					condense( elems, preMap, preFilter, context, xml ) :
					elems,
	
				matcherOut = matcher ?
					// If we have a postFinder, or filtered seed, or non-seed postFilter or preexisting results,
					postFinder || ( seed ? preFilter : preexisting || postFilter ) ?
	
						// ...intermediate processing is necessary
						[] :
	
						// ...otherwise use results directly
						results :
					matcherIn;
	
			// Find primary matches
			if ( matcher ) {
				matcher( matcherIn, matcherOut, context, xml );
			}
	
			// Apply postFilter
			if ( postFilter ) {
				temp = condense( matcherOut, postMap );
				postFilter( temp, [], context, xml );
	
				// Un-match failing elements by moving them back to matcherIn
				i = temp.length;
				while ( i-- ) {
					if ( (elem = temp[i]) ) {
						matcherOut[ postMap[i] ] = !(matcherIn[ postMap[i] ] = elem);
					}
				}
			}
	
			if ( seed ) {
				if ( postFinder || preFilter ) {
					if ( postFinder ) {
						// Get the final matcherOut by condensing this intermediate into postFinder contexts
						temp = [];
						i = matcherOut.length;
						while ( i-- ) {
							if ( (elem = matcherOut[i]) ) {
								// Restore matcherIn since elem is not yet a final match
								temp.push( (matcherIn[i] = elem) );
							}
						}
						postFinder( null, (matcherOut = []), temp, xml );
					}
	
					// Move matched elements from seed to results to keep them synchronized
					i = matcherOut.length;
					while ( i-- ) {
						if ( (elem = matcherOut[i]) &&
							(temp = postFinder ? indexOf.call( seed, elem ) : preMap[i]) > -1 ) {
	
							seed[temp] = !(results[temp] = elem);
						}
					}
				}
	
			// Add elements to results, through postFinder if defined
			} else {
				matcherOut = condense(
					matcherOut === results ?
						matcherOut.splice( preexisting, matcherOut.length ) :
						matcherOut
				);
				if ( postFinder ) {
					postFinder( null, results, matcherOut, xml );
				} else {
					push.apply( results, matcherOut );
				}
			}
		});
	}
	
	function matcherFromTokens( tokens ) {
		var checkContext, matcher, j,
			len = tokens.length,
			leadingRelative = Expr.relative[ tokens[0].type ],
			implicitRelative = leadingRelative || Expr.relative[" "],
			i = leadingRelative ? 1 : 0,
	
			// The foundational matcher ensures that elements are reachable from top-level context(s)
			matchContext = addCombinator( function( elem ) {
				return elem === checkContext;
			}, implicitRelative, true ),
			matchAnyContext = addCombinator( function( elem ) {
				return indexOf.call( checkContext, elem ) > -1;
			}, implicitRelative, true ),
			matchers = [ function( elem, context, xml ) {
				return ( !leadingRelative && ( xml || context !== outermostContext ) ) || (
					(checkContext = context).nodeType ?
						matchContext( elem, context, xml ) :
						matchAnyContext( elem, context, xml ) );
			} ];
	
		for ( ; i < len; i++ ) {
			if ( (matcher = Expr.relative[ tokens[i].type ]) ) {
				matchers = [ addCombinator(elementMatcher( matchers ), matcher) ];
			} else {
				matcher = Expr.filter[ tokens[i].type ].apply( null, tokens[i].matches );
	
				// Return special upon seeing a positional matcher
				if ( matcher[ expando ] ) {
					// Find the next relative operator (if any) for proper handling
					j = ++i;
					for ( ; j < len; j++ ) {
						if ( Expr.relative[ tokens[j].type ] ) {
							break;
						}
					}
					return setMatcher(
						i > 1 && elementMatcher( matchers ),
						i > 1 && toSelector(
							// If the preceding token was a descendant combinator, insert an implicit any-element `*`
							tokens.slice( 0, i - 1 ).concat({ value: tokens[ i - 2 ].type === " " ? "*" : "" })
						).replace( rtrim, "$1" ),
						matcher,
						i < j && matcherFromTokens( tokens.slice( i, j ) ),
						j < len && matcherFromTokens( (tokens = tokens.slice( j )) ),
						j < len && toSelector( tokens )
					);
				}
				matchers.push( matcher );
			}
		}
	
		return elementMatcher( matchers );
	}
	
	function matcherFromGroupMatchers( elementMatchers, setMatchers ) {
		// A counter to specify which element is currently being matched
		var matcherCachedRuns = 0,
			bySet = setMatchers.length > 0,
			byElement = elementMatchers.length > 0,
			superMatcher = function( seed, context, xml, results, outermost ) {
				var elem, j, matcher,
					matchedCount = 0,
					i = "0",
					unmatched = seed && [],
					setMatched = [],
					contextBackup = outermostContext,
					// We must always have either seed elements or outermost context
					elems = seed || byElement && Expr.find["TAG"]( "*", outermost ),
					// Use integer dirruns iff this is the outermost matcher
					dirrunsUnique = (dirruns += contextBackup == null ? 1 : Math.random() || 0.1),
					len = elems.length;
	
				if ( outermost ) {
					outermostContext = context !== document && context;
					cachedruns = matcherCachedRuns;
				}
	
				// Add elements passing elementMatchers directly to results
				// Keep `i` a string if there are no elements so `matchedCount` will be "00" below
				// Support: IE<9, Safari
				// Tolerate NodeList properties (IE: "length"; Safari: <number>) matching elements by id
				for ( ; i !== len && (elem = elems[i]) != null; i++ ) {
					if ( byElement && elem ) {
						j = 0;
						while ( (matcher = elementMatchers[j++]) ) {
							if ( matcher( elem, context, xml ) ) {
								results.push( elem );
								break;
							}
						}
						if ( outermost ) {
							dirruns = dirrunsUnique;
							cachedruns = ++matcherCachedRuns;
						}
					}
	
					// Track unmatched elements for set filters
					if ( bySet ) {
						// They will have gone through all possible matchers
						if ( (elem = !matcher && elem) ) {
							matchedCount--;
						}
	
						// Lengthen the array for every element, matched or not
						if ( seed ) {
							unmatched.push( elem );
						}
					}
				}
	
				// Apply set filters to unmatched elements
				matchedCount += i;
				if ( bySet && i !== matchedCount ) {
					j = 0;
					while ( (matcher = setMatchers[j++]) ) {
						matcher( unmatched, setMatched, context, xml );
					}
	
					if ( seed ) {
						// Reintegrate element matches to eliminate the need for sorting
						if ( matchedCount > 0 ) {
							while ( i-- ) {
								if ( !(unmatched[i] || setMatched[i]) ) {
									setMatched[i] = pop.call( results );
								}
							}
						}
	
						// Discard index placeholder values to get only actual matches
						setMatched = condense( setMatched );
					}
	
					// Add matches to results
					push.apply( results, setMatched );
	
					// Seedless set matches succeeding multiple successful matchers stipulate sorting
					if ( outermost && !seed && setMatched.length > 0 &&
						( matchedCount + setMatchers.length ) > 1 ) {
	
						Sizzle.uniqueSort( results );
					}
				}
	
				// Override manipulation of globals by nested matchers
				if ( outermost ) {
					dirruns = dirrunsUnique;
					outermostContext = contextBackup;
				}
	
				return unmatched;
			};
	
		return bySet ?
			markFunction( superMatcher ) :
			superMatcher;
	}
	
	compile = Sizzle.compile = function( selector, group /* Internal Use Only */ ) {
		var i,
			setMatchers = [],
			elementMatchers = [],
			cached = compilerCache[ selector + " " ];
	
		if ( !cached ) {
			// Generate a function of recursive functions that can be used to check each element
			if ( !group ) {
				group = tokenize( selector );
			}
			i = group.length;
			while ( i-- ) {
				cached = matcherFromTokens( group[i] );
				if ( cached[ expando ] ) {
					setMatchers.push( cached );
				} else {
					elementMatchers.push( cached );
				}
			}
	
			// Cache the compiled function
			cached = compilerCache( selector, matcherFromGroupMatchers( elementMatchers, setMatchers ) );
		}
		return cached;
	};
	
	function multipleContexts( selector, contexts, results ) {
		var i = 0,
			len = contexts.length;
		for ( ; i < len; i++ ) {
			Sizzle( selector, contexts[i], results );
		}
		return results;
	}
	
	function select( selector, context, results, seed ) {
		var i, tokens, token, type, find,
			match = tokenize( selector );
	
		if ( !seed ) {
			// Try to minimize operations if there is only one group
			if ( match.length === 1 ) {
	
				// Take a shortcut and set the context if the root selector is an ID
				tokens = match[0] = match[0].slice( 0 );
				if ( tokens.length > 2 && (token = tokens[0]).type === "ID" &&
						support.getById && context.nodeType === 9 && documentIsHTML &&
						Expr.relative[ tokens[1].type ] ) {
	
					context = ( Expr.find["ID"]( token.matches[0].replace(runescape, funescape), context ) || [] )[0];
					if ( !context ) {
						return results;
					}
					selector = selector.slice( tokens.shift().value.length );
				}
	
				// Fetch a seed set for right-to-left matching
				i = matchExpr["needsContext"].test( selector ) ? 0 : tokens.length;
				while ( i-- ) {
					token = tokens[i];
	
					// Abort if we hit a combinator
					if ( Expr.relative[ (type = token.type) ] ) {
						break;
					}
					if ( (find = Expr.find[ type ]) ) {
						// Search, expanding context for leading sibling combinators
						if ( (seed = find(
							token.matches[0].replace( runescape, funescape ),
							rsibling.test( tokens[0].type ) && testContext( context.parentNode ) || context
						)) ) {
	
							// If seed is empty or no tokens remain, we can return early
							tokens.splice( i, 1 );
							selector = seed.length && toSelector( tokens );
							if ( !selector ) {
								push.apply( results, seed );
								return results;
							}
	
							break;
						}
					}
				}
			}
		}
	
		// Compile and execute a filtering function
		// Provide `match` to avoid retokenization if we modified the selector above
		compile( selector, match )(
			seed,
			context,
			!documentIsHTML,
			results,
			rsibling.test( selector ) && testContext( context.parentNode ) || context
		);
		return results;
	}
	
	// One-time assignments
	
	// Sort stability
	support.sortStable = expando.split("").sort( sortOrder ).join("") === expando;
	
	// Support: Chrome<14
	// Always assume duplicates if they aren't passed to the comparison function
	support.detectDuplicates = !!hasDuplicate;
	
	// Initialize against the default document
	setDocument();
	
	// Support: Webkit<537.32 - Safari 6.0.3/Chrome 25 (fixed in Chrome 27)
	// Detached nodes confoundingly follow *each other*
	support.sortDetached = assert(function( div1 ) {
		// Should return 1, but returns 4 (following)
		return div1.compareDocumentPosition( document.createElement("div") ) & 1;
	});
	
	// Support: IE<8
	// Prevent attribute/property "interpolation"
	// http://msdn.microsoft.com/en-us/library/ms536429%28VS.85%29.aspx
	if ( !assert(function( div ) {
		div.innerHTML = "<a href='#'></a>";
		return div.firstChild.getAttribute("href") === "#" ;
	}) ) {
		addHandle( "type|href|height|width", function( elem, name, isXML ) {
			if ( !isXML ) {
				return elem.getAttribute( name, name.toLowerCase() === "type" ? 1 : 2 );
			}
		});
	}
	
	// Support: IE<9
	// Use defaultValue in place of getAttribute("value")
	if ( !support.attributes || !assert(function( div ) {
		div.innerHTML = "<input/>";
		div.firstChild.setAttribute( "value", "" );
		return div.firstChild.getAttribute( "value" ) === "";
	}) ) {
		addHandle( "value", function( elem, name, isXML ) {
			if ( !isXML && elem.nodeName.toLowerCase() === "input" ) {
				return elem.defaultValue;
			}
		});
	}
	
	// Support: IE<9
	// Use getAttributeNode to fetch booleans when getAttribute lies
	if ( !assert(function( div ) {
		return div.getAttribute("disabled") == null;
	}) ) {
		addHandle( booleans, function( elem, name, isXML ) {
			var val;
			if ( !isXML ) {
				return elem[ name ] === true ? name.toLowerCase() :
						(val = elem.getAttributeNode( name )) && val.specified ?
						val.value :
					null;
			}
		});
	}
	jBud.find = Sizzle;
	jBud.expr = Sizzle.selectors;
	jBud.unique = Sizzle.uniqueSort;
	jBud.text = Sizzle.getText;
	jBud.isXMLDoc = Sizzle.isXML;
	jBud.contains = Sizzle.contains;
	})( window );
	
	
	/**
	 * 定义所有数据类型
	 */
	var dataTypes = ["Object","Boolean","Number","String","Function","Array","Date","RegExp","Error"];
	var class2type = {};
	var regexps = {
			number: /^[0-9]+(.[0-9]+)?$/g,
			opacity:/opacity\s*=\s*([^)]*)/i
	};
	var classHasProperty=class2type.hasOwnProperty;
	for(var i = 0;i<dataTypes.length;i++){
		var n = dataTypes[i];
		class2type[ "[object " + n + "]" ] = n.toLowerCase();
	}
	/**
	 * 浏览器类型
	 */
	
	/**
	 * 类型
	 */
	jBud.type = function(obj) {
		if(obj === null || obj === undefined) {
			return String(obj);
		}
		var v =class2type[class2type.toString.call(obj)]; 
		return v ? v : typeof obj;
	};
	/**
	 * 是否为window对象
	 */
	jBud.isWindow = function(obj){ return obj != null && obj == obj.window; };
	jBud.getWindow = function(obj){return jBud.isWindow(obj) ?obj :obj.nodeType === 9 ?obj.defaultView || obj.parentWindow :false;};
	jBud.isDocument = function(obj) {return obj != null && obj == obj.ownerDocument;};
	/**
	 * 是否空白对象
	 */
	jBud.isPlainObject = function(obj){
		if ( !obj || jBud.type(obj) !== "object" || obj.nodeType || jBud.isWindow( obj ) ) {
			return false;
		}
		try {
			if ( obj.constructor &&
				!classHasProperty.call(obj, "constructor") &&
				!classHasProperty.call(obj.constructor.prototype, "isPrototypeOf") ) {
				return false;
			}
		} catch ( e ) {
			return false;
		}
		var key;
		for ( key in obj );
		return key === undefined || classHasProperty.call( obj, key );
	};
	
	/**
	 * each遍历
	 */
	jBud.each = function(obj,callback){
		if(!jBud.isIterator(obj) || jBud.type(callback) !== 'function') return ;
		for(var i = 0;i<obj.length;i++){
			var b = callback.call(obj[i],i,obj[i]);
			if(b === false) break;
		}
	};
	/**
	 * 参数过滤
	 */
	jBud.parameter = function(args,params,match){
		for(var i = 0;i<match.length;i++) {
			var m = match[i];
			var r = false;
			for(var j = 0;j<args.length;j++){
				var arg = args[j];
				if(typeof arg === m.type) {
					params[m.name] = arg;
					args.splice(j,1);
					r = true;
					break;
				}
			}
			if(m.require && !r) {
				throw new Error("miss params at "+i+" , named : "+m.name);
			}
		}
		args.splice(0,args.length);
		args = null;
		match = null;
		return params;
	};
	/**
	 * 重载对象类型
	 */
	jBud.extend = function(){
		var src,from,key,froms,deep=false,target=arguments[0]||{},i=1,length = arguments.length;
		if(typeof target === "boolean") {
			deep = target,target = arguments[1]||{},i=2;
		}
		if(typeof target !== 'object' && !jBud.isPlainObject(target)) {
			target = {};
		}
		if(length <= i) {
			target = this;//如果没有目的，那么默认给自己安装方法
			--i;
		}
		for(;i<length;i++){
			if((froms = arguments[i]) == null) continue;
			for(key in froms){
				src = target[key];
				from = froms[key];
				if(from === undefined || src === from) continue;
				if(deep && jBud.isPlainObject(from)) {
					var isArray = jBud.type(from) === 'array';
					if(isArray) {
						src = src && jBud.type(src) === 'array' ? src : [];
					} else {
						src = src && jBud.isPlainObject(src) ? src : {};
					}
					target[key] = jBud.extend(deep,src,from);
				} else {
					target[key] = from;
				}
			}
		}
		return target;
	};
	
	/**
	 * 数据类型扩展
	 */
	jBud.extend({
		isArray:function(obj) {return jBud.type(obj) === "array";},
		isFunction:function(obj) {return jBud.type(obj) === "function";},
		isNumeric:function(obj){return jBud.type(obj) === "number";},
		isBoolean:function(obj){return jBud.type(obj) === "boolean";},
		isString:function(obj){return jBud.type(obj) === "string";},
		isDate:function(obj){return jBud.type(obj) === "date";},
		isError:function(obj){return jBud.type(obj) === "error";},
		isRegExp:function(obj){return jBud.type(obj) === "regexp";},
		isObject:function(obj){return jBud.type(obj) === "object";},
		isEmpty:function(obj){var r = jBud.type(obj); return r === "null" || r === "undefined";},
		isBudObject:function(obj){return obj instanceof jBud.seed.instance;},
		isIterator:function(obj){
			if(jBud.isArray(obj)) return true;
			return obj && jBud.isNumeric(obj.length);
		},
		isHTMLElement:function(obj){return obj && obj === document.body.parentNode;},
		isBodyElement:function(obj){return obj && obj === document.body;},
		isHTMLOrBody:function(obj){return this.isHTMLElement(obj) || this.isBodyElement(obj);}
	});
	/**
	 * 数值类型处理扩展
	 */
	var num2hex=['0','1','2','3','4','5','6','7','8','9','A','B','C','D','E','F'];
	jBud.extend({
		encodeDecimal:function(n,d,l) {
			if(!jBud.isNumeric(n) || !jBud.isNumeric(d)) {return false;}
			if(jBud.isEmpty(l) || !jBud.isNumeric(l)) l = 0;
			var r="";
			if(n<=1 || n>16){return false;}
			var b = 0;
			do{
				b = parseInt(d)%parseInt(n);
				d /= n;
				r = num2hex[b]+r;
			}while(d>= 1);
			if(r.length<l){
				var c = l - r.length;
				for(var i = 0;i<c;i++){
					r = "0"+r;
				}
			}
			return r;
		},
		decodeDecimal:function(b,d){
			if(jBud.isEmpty(d) || jBud.isEmpty(b)) return 0;
			if(!jBud.isNumeric(b) || b <= 0 || b >16){return 0;}
			var r = 0,i=0,v = 0,c = 0;
			for(i=d.length-1;i>=0;i--){
				var v = jBud.indexOf(num2hex,d[i]);
				if(v === -1) return 0;
				r += v*Math.pow(b,c++);
			}
			return r;
		},
		bin:function(d,l){return this.encodeDecimal(2,d,l);},
		oct:function(d,l){return this.encodeDecimal(8,d,l);},
		hex:function(d,l){return this.encodeDecimal(16,d,l);},
		shex:function(s,l){
			var _s = "";
			for(var i = 0;i<s.length;i++){
				_s += s.charCodeAt(i);
			}
			return jBud.hex(parseInt(_s),l);
		}
	});
	
	/**
	 * 字符串类型处理扩展
	 */
	jBud.extend({
		trim:function(str){
			if(jBud.isString(str)) return str.replace(/(^\s*)|(\s*$)/g, "");
		},
		ltrim:function(str){
			if(jBud.isString(str)) return str.replace(/(^\s*)/g, "");
		},
		rtrim:function(str){
			if(jBud.isString(str)) return str.replace(/(\s*$)/g, "");
		},
		equals:function(s1,s2,ig){
			if(!jBud.isString(s1) || !jBud.isString(s2)) return false;
			if(!ig) return s1 === s2;
			else return s1.toLowerCase() === s2.toLowerCase();
		},
		uuid:function(){
			// #012 修改UUID算法
			var j = "",t,r,p,e;
			t = jBud.hex(new Date().getTime(),12),
			r = jBud.hex(parseInt(Math.random()*65535),4),
			p = jBud.hex(parseInt(Math.random()*65535),4);
			e = jBud.hex(parseInt(Math.random()*9223372036854775807),8);
			j += t.substring(0,8)+t.substring(8)+r+p+e;
			return j;
		},
		guid:function(){return jBud.uuid();},
		isHTML:function(str){
			if(typeof str === 'string') {
				return str.charAt(0) === '<' && str.charAt(str.length-1) === '>';
			}
			return false;
		},
		noWhite:function(text,isArray){
			if(typeof text !== 'string') return text;
			var ns = text.match(/\S+/g) || [];
			return isArray?ns:ns.join(" ");
		}
	});
	/**
	 * 数组处理方法
	 */
	jBud.extend({
		merge:function(to,from,ignoreTo){
			if((!jBud.isIterator(to) || !jBud.isIterator(from)) && !ignoreTo) return to;
			if(!ignoreTo) for(var i = 0;i<from.length;i++) to.push(from[i]);
			else {
				var tl = to.length,fl = from.length,i = 0;
				if(!jBud.isNumeric(tl)) tl = 0;
				if(!jBud.isNumeric(fl)) fl = 0;
				for(;i<fl;i++) to[tl++] = from[i];
				to.length = i;
			}
			return to;
		},
		indexOf:function(a,v){
			for(var i = 0;i<a.length;i++){
				if(a[i] == v){return i;}
			}
			return -1;
		},
		lastIndexOf:function(a,v){
			for(var i = a.length-1;i>=0;i--){
				if(a[i] == v){return i;}
			}
			return -1;
		},
		inArray:function(v,a){
			return this.indexOf(a,v);
		}
	});
	jBud.extend({
		bud:function(elem){
			if(!elem) return undefined;
			var bud = elem.__jbud__;
			if(!bud) {elem.__jbud__ = {};bud = elem.__jbud__;}
			return bud;
		}
	});
	/**
	 * 事件UUID
	 */
	jBud.euid = 1;
	jBud.duid = 1;
	/**
	 * 事件中的方法，通过HASH方式绑定事件，逃避IE内存泄露问题
	 */
	jBud.event = {
			mapName:"__FIREMAP__",
			/**
			 * 添加事件
			 */
			add:function(elem,type,handler,data,selector,one){
				var elemBud = jBud.bud(elem),evts = elemBud.events,handlers,handle,obj,fireMap,registered;
				//控制器ID
				if(!handler.juid) handler.juid = jBud.euid++;
				//事件HASH
				if(!evts) evts = elemBud.events={};
				//获得某一事件队列	
				handlers = evts[type];
				registered = !!handlers;
				elemBud.elem = elem;
				if(!handlers) handlers = evts[type] = {};
				fireMap = handlers[this.mapName];
				if(!fireMap) fireMap = handlers[this.mapName] = {};
				handlers[handler.juid] = handler;
				obj = {
					type:type,
					data:data,
					juid:handler.juid,
					handler:handler,
					elem:elem,
					one:one,
					selector:jBud.noWhite(selector)
				};
				if(!handler.fires) {handler.fires = {};handler.fuid = 1;}
				handler.fires[handler.fuid] = obj;
				if(!fireMap[handler.juid]) fireMap[handler.juid] = {};
				obj.fuid = handler.fuid;
				fireMap[handler.juid][handler.fuid++] = obj;
				if(!(handle = elemBud.handle)) {
					handle = elemBud.handle = function(event) {
						return jBud.event.handle.apply(elemBud.elem,arguments);
					};
				}
				// #003 解决在IE条件下重复追事件的问题,fixed。
				if(registered) return ;
				if(elem.addEventListener) {
					elem.addEventListener(type,handle,false);
				} else {
					elem.attachEvent("on"+type,handle);
				}
			},
			/**
			 * 统一处理事件函数
			 */
			handle:function(event){
				var type = event.type,events = jBud.bud(this).events,handlers = events[type],self = this,fireMap,map;
				if(!handlers) return ;
				// #002 修正重复无条件的执行所有的handler事件
				fireMap = handlers[jBud.event.mapName];
				if(!fireMap) return ;
				for(var k in fireMap){
					var fires = fireMap[k],e,handler;
					if(!fires) continue;
					for(var h in fires) {
						var fire = fires[h],e = jBud.event.filter(event,fire.handler,this,fire.guid),handler = handlers[fire.juid];
						e.data = fire.data;
						if(fire.selector) {
							var subs = jBud(self).find(fire.selector);
							subs.each(function(index){
								if(this === e.target) {
									fire.handler.call(self,e);
									if(fire.one) {
										delete fires[h];
										delete handler.fires[h];
									}
									return false;
								}
							});
							subs = null;
						} else {
							fire.handler.call(self,e);
							if(fire.one) {
								delete fires[h];
								delete handler.fires[h];
							}
						}
					}
				}
			},
			/**
			 * 添加删除触发事件
			 */
			removeFire:function(fire){
				var bud = jBud.bud(fire.elem),events = bud.events,handlers = events[fire.type],juid=fire.juid,fuid=fire.fuid,fireMap = handlers[this.mapName],handler = handlers[juid];
				delete fireMap[juid][fuid];
				delete handler.fires[fuid];
			},
			/**
			 * 删除事件，其中对于委托事件而言，需要特别注意，消除绑定的委托selector必须与绑定时的一致才能有效解除，
			 * 此做法为了提高效率，而放弃有效性
			 */
			remove:function(elem,type,handler,selector){
				var events = jBud.bud(elem).events,handlers,juid,fires,fireMap,map;
				if(!type) {
					delete events;
					jBud.bud(elem).events = {};
					return ;
				}
				handlers = events[type];
				fireMap = handlers[this.mapName];
				if(typeof handler === 'function') {
					if(!selector) {
						if(!handler.juid) return ;
						delete handlers[handler.juid];
						delete fireMap[handler.juid];
					} else {
						selector =  jBud.noWhite(selector),fires = handler.fires,map = fireMap[handler.juid];
						for(var k in fires){
							if(fires[k].selector === selector) {
								delete fires[k];
								delete map[k];
							}
						}
					}
				} else if (handler === undefined){
					if(!selector) {
						delete handlers;
						events[type] = {};
						fireMap = {};
					} else {
						selector =  jBud.noWhite(selector);
						for(var k in handlers){
							var hand = handlers[k],fires = hand.fires,map = fireMap[hand.juid];
							for(var h in fires){
								if(fires[h].selector === selector) {
									delete fires[h];
									delete map[h];
								}
							}
						}
					}
 				}
			},
			/**
			 * 事件过滤器
			 */
			filter:function(event,handler,elem,juid) {
				if(event === undefined || event === null || typeof event != 'object') {
					event = {
							currentTarget:elem,
							target:elem
					};
				};
				var e = event;
				e.originalEvent = e;//兼容jQuery自定义event
				e.which = e.which == undefined ? e.keyCode : e.which;
				e.handler = handler;
				e.currentTarget = this;
				e.target = e.target ? e.target : e.srcElement;
				e.juid = juid;
				e.stopPropagation = e.stopPropagation || function(){
					this.cancelBubble = true;
				};
				e.preventDefault = e.preventDefault || function(){
					this.returnValue = false;
				};
				return e;
			},
			fires:function(elem,type){
				var bud,events,fires,fs;
				if(!elem || !(bud = jBud.bud(elem))) return undefined;
				var events = bud.events;
				if(!events || !events[type]) return undefined;
				fires = [];
				var handlers = events[type];
				var fireMap = handlers[this.mapName];
				for(var k in fireMap) {
					fs = fireMap[k];
					for(var j in fs) fires.push(fs[j]);
				}
				if(!fires) return undefined;
				return fires;
			}
	};
	
	jBud.style = {
			add:function(elem,name,index,fn) {
				var cn = elem.className,cna = jBud.noWhite(cn,true),cns = cna.join(" ");
				if(fn) {
					var nc = fn(index,cns);
					if(typeof nc !== 'string' || (nc = jBud.trim(nc)).length <= 0) return true;
					name = jBud.noWhite(nc,true);
				} 
				jBud.each(name,function(){
					var reg = new RegExp("\\b"+this+"\\b");
					if(!reg.test(cns)) cna.push(this);
					reg = undefined;
				});
				elem.className = cna.join(" ");
				delete cna;cns = undefined;
			},
			remove:function(elem,name,index,fn){
				var cn = elem.className;
				if(fn) {
					var nc = fn(index,cn);
					if(typeof nc !== 'string' || (nc = jBud.trim(nc)).length <= 0) return true;
					name = jBud.noWhite(nc,true);
				}
				jBud.each(name,function(){
					var reg = new RegExp("\\b"+this+"\\b");
					cn = cn.replace(reg,"");
					reg = undefined;
				});
				elem.className = cn;
			},
			has:function(elem,name){
				var reg = new RegExp("\\b"+jBud.trim(name)+"\\b");
				return reg.test(elem.className);
			},
			toggle:function(elem,name,flag){
				var budElem = jBud.bud(elem),tcs = budElem.toggleClass,i = 0,className,classNames,has,state;
				if(!budElem.toggleClass) {tcs = budElem.toggleClass = [];}
				if(name === undefined) {
					name = jBud.noWhite(elem.className,true);
					if(name.length === 0) name = tcs.slice(0,tcs.length);
				} else {
					name = jBud.noWhite(name,true);
				}
				tcs.splice(0,tcs.length);
				while((className = name[i++])){
					has = jBud.style.has(elem,className);
					state = flag !== undefined ? flag : !has;
					jBud.style[state?'add':'remove'](elem,jBud.noWhite(className,true));
				}
				budElem.toggleClass = name;
			},
			style2postion:["Top","Right","Bottom","Left"],
			getStyle:function(elem,flag){
				return flag ? elem.style : (elem.currentStyle || window.getComputedStyle(elem,null));
			},
			value:function(elem,prefix,suffix,pos) {
				if(jBud.isWindow(elem)) return 0;
				var r = 0,s2p=jBud.style.style2postion,style = this.getStyle(elem);
				if(!pos) return null;
				for(var i = 0;i<pos.length;i++) {
					var v = parseFloat(style[prefix+s2p[pos[i]]+suffix]);
					r += isNaN(v)?0:v;
				}
				return r;
			},
			padding:function(elem,pos){
				return this.value(elem,"padding","",pos);
			},
			margin:function(elem,pos){
				return this.value(elem,'margin','',pos);
			},
			border:function(elem,pos){
				return this.value(elem,'border','Width',pos);
			},
			mbp:function(elem,pos){
				return this.margin(elem,pos)+this.padding(elem,pos)+this.border(elem,pos);
			},
			mb:function(elem,pos){
				return this.margin(elem,pos)+this.border(elem,pos);
			},
			defpx:function(value) {
				return regexps.number.test(value) ? value+"px":value;
			},
			offset:function(elem) {
				var r,win,doc,docElem,value;
				if(!elem) return undefined;
				if(elem == document || jBud.isWindow(elem)) return undefined;
				if ( typeof elem.getBoundingClientRect !== 'undefined' ) {
					value = elem.getBoundingClientRect();
				}
				win = jBud.getWindow(document),docElem = document.documentElement;
				r =  {top: value.top  + ( win.pageYOffset || docElem.scrollTop )  - ( docElem.clientTop  || 0 ),	left: value.left + ( win.pageXOffset || docElem.scrollLeft ) - ( docElem.clientLeft || 0 )};
				return r;
			},
			setOffset:function(elem,set,index){
				var pos = this.get(elem,'position'),offset,top,left,defSet,position;
				if(!pos || pos === 'static') {pos = elem.style.position = "relative";}
				offset = this.offset(elem);
				if(offset === undefined) return undefined;
				top = this.get(elem,"top"),left = this.get(elem,"left");
				defSet = ( pos === "absolute" || pos === "fixed" ) && jBud.inArray("auto", [top, left]) > -1;
				if(defSet) {
					position = this.position(elem),top = position.top,left = position.left;
				} else {
					top = parseFloat(top) || 0, left = parseFloat(left) || 0;
				}
				if ( set.top != null ) {
					elem.style.top = (set.top - offset.top + top)+"px";
				}
				if ( set.left != null ) {
					elem.style.left = (set.left - offset.left + left)+"px";
				}
			},
			offsetParent:function(elem){
				var offsetParent = elem.offsetParent || document.documentElement;
				while ( offsetParent && ( !jBud.isHTMLElement( offsetParent ) && this.get( offsetParent, "position") === "static" ) ) {
					offsetParent = offsetParent.offsetParent;
				}
				return offsetParent || document.documentElement;
			},
			position:function(elem){
				var offsetParent,offset,parentOffset;
				if(!elem) return undefined;
				if(elem == document || jBud.isWindow(elem)) return undefined;
				offsetParent = this.offsetParent(elem);
				if ( this.get( elem, "position" ) === "fixed" ) {
					offset = elem.getBoundingClientRect();
				} else {
					offset = this.offset(elem);
					parentOffset = {top:0,left:0};
					if ( !jBud.isHTMLElement( offsetParent) ) {
						parentOffset = this.offset(offsetParent);
					}
					parentOffset.top  += this.border(offsetParent,[0]);
					parentOffset.left += this.border(offsetParent,[3]);
				}
				return {
					top:  offset.top  - parentOffset.top - this.margin( elem, [0]),
					left: offset.left - parentOffset.left - this.margin( elem, [3])
				};
			},
			ie2filter:{
				"opacity":function(style,value,elem){
					value = parseFloat(value);
					// #008 对于IE7一下浏览器，不支持opacity属性直接赋值
					if("opacity" in style) {
						style["opacity"] = value;
					}
					if(value !== undefined && !isNaN(value)) {
						if(regexps.opacity.test(style.filter)) {
							// #009 解决IE8-浏览器无法正常支持透明的计算
							style.filter = style.filter.replace(regexps.opacity,"opacity="+(value*100));
						} else {
							style.filter += "alpha(opacity="+(value*100)+")";
						}
						return ;
					}
					return regexps.opacity.test(style.filter) ? RegExp.$1 * 0.01 : 1;
				}
			},
			getPropertyValue:function(style,name){
				var r = style[name] || (style.getPropertyValue?style.getPropertyValue(name):undefined);
				if(r !== undefined) return r;
				var iname = name.toLowerCase(),handler;
				if((handler = this.ie2filter[iname])) r = handler(style);
				return r;
			},
			get:function(elem,name,flag){
				var style = this.getStyle(elem,flag);
				if(!style) return undefined;
				if(jBud.isArray(name)) {
					var props = {};
					for(var k in name) {
						props[name[k]] = this.getPropertyValue(style,name[k]);
					}
					return props;
				} else return this.getPropertyValue(style,name); 
			},
			set:function(elem,name,value){
				var style = this.getStyle(elem,true);
				if(!style) return undefined;
				var iname = name.toLowerCase(),handler;
				if((handler = this.ie2filter[iname])) handler(style,value,elem);
				else {
					try {
						style[name] = value;
					} catch(err) {}
				} 
			}
	};
	jBud.dom = {
			memory:function(html){
				var fragment = document.createDocumentFragment();
				var con = document.createElement("div");
				con.innerHTML = html;
				return jBud.merge([],con.childNodes);
			},
			empty:function(elem){
				if(!elem) return ;
				var children = elem.childNodes,k,node,t;
				for(k = children.length-1;k>=0;k--) {
					if(children[k]) elem.removeChild(children[k]);
				}
			},
			clone:function(elem){
				var node;
				if(elem.cloneNode) node = elem.cloneNode(true);
				else {
					var fragment = document.createDocumentFragment();
					var div = document.createElement("div");
					fragment.appendChild(div);
					div.innerHTML = elem.outerHTML;
					node = fragment.firstChild;
					fragment.removeChild(node);
				}
				return node;
			},
			control:function(elem,nodes,index,stopClone,callback){
				var elems = [],self=this,html,type,isClone;
				if(!jBud.isArray(nodes)) elems.push(nodes);
				else elems = nodes;
				isClone = index < stopClone;
				for(var k in elems){
					html = elems[k],type = typeof html;
					if(type === 'string') this.control(elem,this.memory(html),index,stopClone,callback);
					else if(jBud.isArray(html)) this.control(elem,html,index,stopClone,callback);
					else if(jBud.isBudObject(html)) html.each(function(){callback.call(elem,isClone?self.clone(this):this);});
					else if(this.isElement(html)) callback.call(elem,isClone?self.clone(html):html);
				}
				elems = null;
			},
			nodeName:function(elem,name){
				return elem.nodeName.toUpperCase() === name.toUpperCase();
			},
			siblings: function(elem,n,next,one) {
				var ss = [];
				if(!n) n = elem.firstChild;
				if(typeof next === 'undefined') next = true;
				while (n) {
					if ( n.nodeType === 1 && n !== elem ) {
						ss.push(n);
						if(one) break;
					}
					n = next ? n.nextSibling:n.previousSibling;
				}
				return ss;
			},
			parents:function(elem,one){
				var ss = [],n = elem;
				while (n) {
					if ( n.nodeType === 1 && n !== elem ) {
						ss.push(n);
						if(one) break;
					}
					n = n.parentNode;
				}
				return ss;
			},
			isElement:function(elem){
				return typeof elem ==='object' &&  elem !== undefined && elem !== null && (elem.nodeType === 1 || elem.nodeType === 3 || elem.nodeType === 9 || elem.nodeType === 11);
			}
	};
	jBud.valExtend = {
			select:{
				set:function(elem,val){
					var params,options,op,v;
					if(!jBud.isArray(val)) params = [val];
					else params = val;
					options = elem.options;
					for(var i = 0;i<options.length;i++) {
						op = options[i],v = jBud.valExtend.option.get(op);
						if(jBud.inArray(v,params) >= 0) op.selected = true;
						else op.selected = false;
					}
					return params;
				},
				get:function(elem){
					var type = elem.type,bud;
					if(type) type = type.toUpperCase();
					if((bud=jBud(elem)).prop("multiple") || elem.type === 'select-multiple') {
						var rs = [],options = elem.options;
						for(var i = 0;i<options.length;i++) {
							var op = options[i];
							if(!op.disabled && op.selected) rs.push(op.value);
						}
						return rs;
					}
					return elem.value;
				}
			},
			option:{
				get:function(elem){
					var val = elem.attributes.value;
					return !val || val.specified ? elem.value : elem.text;
				}
			}
	};
	/**
	 * 种子链，为每个Node或者NodeList绑定种子链
	 */
	jBud.seed  = {
			constructor:jBud,//构建对象类型
			/**
			 * 对象实例化
			 * @param {String|Object} selector 选择器，可以是字符串、DOM元素对象、jBud对象以及符合选择器的数组对象
			 * @param {String|Object} context 上下文，同selector参数一致
			 * @return {Object} jBud对象 
			 */
			instance : function(selector,context) {
				var isArray,isBud;
				if(!selector) return this;
				//如果是字符串，那么考虑是否是HTML标签，如果不是那么直接进行获取
				if(typeof selector === "string" || (isArray = jBud.isArray(selector))) {
					var nodes = [];
					//如果是数组则进行遍历
					if(isArray) {
						jBud.each(selector,function(i,item){
							if(typeof item === 'string') {
								jBud.merge(nodes,jBud(item,context));
							} else if (typeof item === 'object') {
								if(item.nodeType || jBud.isWindow(item)) nodes.push(item);
								else if(jBud.isBudObject(item)) jBud.merge(nodes,item);
								else if(jBud.isArray(item)) jBud.merge(nodes,jBud(item,context));
							}
						});
					}else if(jBud.isHTML(selector)) {
						nodes = jBud.dom.memory(selector);
					} else {
						//如果是字符串类型的上下文
						if(typeof context === 'string') {
							jBud.each(jBud.find(context),function(){
								jBud.merge(nodes,jBud.find(selector,this));
							});
						}
						//如果是对象类型
						else if (typeof context === 'object') {
							if(jBud.isBudObject(context)) {
								return context.find(selector);
								//如果是数组类型
							} else if (jBud.isArray(context)) {
								jBud.each(context,function(){
									jBud.merge(nodes,jBud.find(selector,this));
								});
							} else {
								jBud.merge(nodes,jBud.find(selector,context));
							}
						}
						else if (jBud.isEmpty(context)) {
							nodes = jBud.find(selector);
						}
					}
					jBud.merge(this,nodes,true);
					this.selector = selector;
					this.jbud = true;
					return this;
				} else if(typeof selector === 'object') {
					isBud = jBud.isBudObject(selector);
					if(isBud) return selector;
					else if (selector.nodeType || jBud.isWindow(selector)) {
						jBud.merge(this,[selector],true);
						this.selector = selector;
						this.jbud = true;
						return this;
					}
				} else if (typeof selector === 'function') {
					return jBud.ready(selector);
				}
				return this;
			},
			/**
			 * 遍历循环，只要符合iterator构造方法的对象都可以执行each方法
			 * @param {Function} callback 回调函数，如果返回值为false，那么执行中断操作
			 * @return 返回当前jBud对象
			 */
			each:function(callback){
				if(!jBud.isFunction(callback)) return ;
				jBud.each(this,callback);
				return this;
			},
			/**
			 * 在当前作用域下查找子节点
			 * @param {String|Object} selector 选择器
			 * @return {Object} jBud对象
			 */
			find:function(selector) {
				var obj = new jBud.seed.instance();
				if(!selector) return obj;
				var nodes = [];
				this.each(function(){
					jBud.merge(nodes,jBud.find(selector,this));
				});
				jBud.merge(obj,nodes,true);
				obj.selector = selector;
				obj.jbud = true;
				return obj;
			},
			/**
			 * 委托注册事件
			 */
			delegate:function(){
				var selector = arguments[0],type = arguments[1],data = arguments[2], handler=arguments[3];
				return this.on(type,selector,data,handler);
			},
			/**
			 * 注册事件
			 */
			on:function(){
				var params = {type:null,selector:null,data:null,handler:null,one:false};
				var match = [{name:"type",type:"string",require:true},{name:"selector",type:"string",require:false},{name:"data",type:"object",require:false},{name:"handler",type:"function",require:true},{name:"one",type:"boolean",require:false}];
				var args = jBud.merge([],arguments);
				try {
					params = jBud.parameter(args,params,match);
				} catch(e){
					params = null;
					return this;
				} finally {
					match = null;args = null;
				}
				var self = this;
				this.each(function() {
					jBud.event.add(this,params.type,params.handler,params.data,params.selector,params.one);
				});
				return this;
			},
			/**
			 * 注册一次，执行一次
			 */
			one:function(){	return this.on.call(this,arguments[0],arguments[1],arguments[2],arguments[3],true);},
			/**
			 * 兼容node.js处理方式
			 */
			once:function(){return this.one.apply(this,arguments);},
			/**
			 * 解除事件绑定
			 */
			off:function(type){
				var selector,handler,len = arguments.length,args = arguments;
				if(len == 2) {
					if(typeof args[1] === 'string') selector = args[1];
					else if(typeof args[1] === 'function') handler = args[1];
				} else if ( len  === 3) {
					if(typeof args[1] === 'string') selector = args[1];
					if(typeof args[2] === 'function') handler = args[2];
				}
				this.each(function(){
					jBud.event.remove(this,type,handler,selector);
				});
				return this;
			},
			/**
			 * 通过off方法，同化KISSY方法
			 */
			detach:function(){
				return this.off.apply(this,arguments);
			},
			/**
			 * 通过off方法，同化KISSY方法
			 */
			undelegate:function(){
				return this.off.apply(this,arguments);
			},
			/**
			 * 触发事件
			 */
			trigger:function(type,params){
				return this.each(function(){
					var fires = jBud.event.fires(this,type);
					if(this[type]) {
						try{
							//#004 解决在触发本有事件时，数据没有传递的问题
							if(fires) for(k in fires) if(typeof params !== 'undefined') fires[k].data = params;
							this[type].call(this);
							delete fires;
						}catch(e){}
						return true;
					};
					if(!fires) return true;
					for(var k in fires) {
						var fire = fires[k];
						if(fire.selector) continue;
						var e = jBud.event.filter(undefined,fire.handler,this,fire.juid);
						e.type = type;
						if(typeof params !== 'undefined')
							e.data = fire.data = params;
						else 
							e.data = fire.data;
						fire.handler.call(fire.elem,e);
						if(fire.one) {
							jBud.event.removeFire(fire);
						}
					}
					delete fires;
				});
			},
			/**
			 * 触发事件，兼容KISSY
			 */
			fire:function(){return this.trigger.apply(this,arguments);},
			/**
			 * 兼容Node.js处理方式
			 */
			emit:function(){return this.trigger.apply(this,arguments);},
			/*#CSS控制 start #*/
			/**
			 *  为DOM添加样式
			 */
			addClass:function() {
				var name = arguments[0],t=typeof name,fn;
				if(!(t === 'function' || t === 'string')) return this;
				if(typeof name === 'function') { fn = name; name = [];}
				if(typeof name === 'string') name = jBud.trim(name);
				name = jBud.noWhite(name,true);
				return this.each(function(index){
					return jBud.style.add(this,name,index,fn);
				});
			},
			/**
			 * 为DOM删除样式
			 */
			removeClass:function(){
				var name = arguments[0],t = typeof name,fn;
				if(!(t === 'function' || t === 'string')) return this;
				if(typeof name === 'function') { fn = name; name = [];}
				if(typeof name === 'string') name = jBud.trim(name);
				name = jBud.noWhite(name,true); 
				return this.each(function(index){
					return jBud.style.remove(this,name,index,fn);
				});
			},
			/**
			 * 是否包含所有的样式内容
			 */
			hasClass:function(){
				var name = arguments[0],result = false,reg;
				if(typeof name !== 'string' || (name = jBud.trim(name)).length <= 0) return true;
				reg = new RegExp("\\b"+name+"\\b");
				this.each(function(){
					if(reg.test(this.className)) {
						result = true;
						return false;
					}
				});
				return result;
			},
			/**
			 * 替换样式
			 */
			toggleClass:function(){
				var name = arguments[0],flag = arguments[1],len=arguments.length,fn=undefined;
				var type = typeof name; 
				if(len > 1) {
					if(typeof flag !== 'boolean') {
						flag = undefined;
					}
				}
				if(type === 'function') {
					fn = name,name =undefined;
					return this.each(function(index){
						return jBud.style.toggle(this,fn.call(index,this.className,flag),flag);
					});
				} else if (type === 'string'){
					name = jBud.noWhite(name,true);
				} else if (type === 'undefined') {
					name = undefined,flag = undefined;
				} else if (type === 'boolean') {
					flag = name, name = undefined;
				}
				return this.each(function(index) {
					return jBud.style.toggle(this,name,flag);
				});
			},
			/**
			 * 宽度设定
			 */
			width:function(){
				var pos=[1,3],style=jBud.style,value = arguments[0],isSet= value !== undefined,elem,doc;
				if(!isSet) {
					if(this.length <= 0) return null;
					elem = this[0],doc = document.documentElement;
					if(jBud.isWindow(elem)) return doc.clientWidth;
					if(jBud.isDocument(elem)) return Math.max(doc.scrollWidth,doc.clientWidth);
					return elem.offsetWidth-style.padding(elem,pos)-style.value(elem,"border","Width",pos);
				}
				value = style.defpx(value);
				return this.each(function(index) {
					try {
						this.style.width = value;
					} catch(err) {}
				});
			},
			/**
			 * 高度设定
			 */
			height:function(){
				var pos=[0,2],style=jBud.style,value = arguments[0],isSet= value !== undefined,elem,doc;
				if(!isSet) {
					if(this.length <= 0) return null;
					elem = this[0],doc = document.documentElement;
					//#013 修改对于window获取高度时，在IE8-浏览器中的bug问题
					if(jBud.isWindow(elem)) {
						return doc.clientHeight;
					}
					if(elem == elem.ownerDocument) {
						return Math.max(doc.scrollHeight,doc.clientHeight);
					}
					return elem.offsetHeight-style.padding(elem,pos)-style.value(elem,"border","Width",pos);
				}
				value = style.defpx(value);
				return this.each(function(index) {
					try {
						this.style.height = value;
					} catch(err) {}
					
				});
			},
			/**
			 * 边框的水平宽度
			 */
			borderWidth : function() {
				return this.borderValue([1,3]);
			},
			
			/**
			 * 边框的垂直宽度
			 */
			borderHeight : function(){
				return this.borderValue([0,2]);
			},
			
			/**
			 * 边框方向的宽度值
			 */
			borderValue : function(value) {
				if(!this[0] || !jBud.isArray(value)) return undefined;
				return jBud.style.value(this[0],"border","Width",value);
			},
			
			/**
			 * 内宽度
			 */
			innerWidth:function(){
				var style=jBud.style,pos=[1,3],elem;
				if(this.length<=0) return  null;
				elem = this[0];
				if(elem == document || jBud.isWindow(elem)) return jBud(elem).width();
				return elem.offsetWidth-style.value(elem,"border","Width",pos);
			},
			/**
			 * 内高度
			 */
			innerHeight:function(){
				var style=jBud.style,pos=[0,2],elem;
				if(this.length <= 0) return null;
				elem = this[0];
				if(elem == document || jBud.isWindow(elem)) return jBud(elem).height();
				return elem.offsetHeight-style.value(elem,"border","Width",pos);
			},
			/**
			 * 外宽度
			 */
			outerWidth:function(margin){
				var style=jBud.style,pos=[1,3],elem;
				if(this.length <= 0) return null;
				elem = this[0];
				if(elem == document || jBud.isWindow(elem)) return jBud(elem).width();
				return elem.offsetWidth+(margin?style.margin(elem,pos):0);
			},
			/**
			 * 外高度
			 */
			outerHeight:function(margin){
				var style=jBud.style,pos=[0,2],elem;
				if(this.length <= 0) return null;
				elem = this[0];
				if(elem == document || jBud.isWindow(elem)) return jBud(elem).height();
				return elem.offsetHeight+(margin?style.margin(elem,pos):0);
			},
			/**
			 * 滚动高度与宽度
			 */
			scroll:function(){
				var style=jBud.style,value = arguments[0],isSet= value !== undefined,elem,doc,left,top;
				if(!isSet) {
					if(this.length <= 0) return 0;
					elem = this[0],doc = document.documentElement;
					if(jBud.isWindow(elem) || elem == document) return {left:doc.scrollLeft,top:doc.scrollTop};
					return {left:elem.scrollLeft,top:elem.scrollTop};
				}
				var def = {left:undefined,top:undefined};jBud.extend(def,value);left = def.left,top=def.top;
				left = left === undefined ? left : isNaN(parseFloat(left))?0:parseFloat(left),def.left=left;
				top = top === undefined ? top : isNaN(parseFloat(top))?0:parseFloat(top),def.top=top;
				return this.each(function(index){
					if(jBud.isWindow(this) || this == document) {
						doc = document.documentElement;
						if(def.left !== undefined) doc.scrollLeft = def.left;
						if(def.top !== undefined) doc.scrollTop = def.top;
					} else {
						if(def.left !== undefined) this.scrollLeft = def.left;
						if(def.top !== undefined) this.scrollTop = def.top;
					}
				});
			},
			/**
			 * 左滚动宽度
			 */
			scrollLeft:function(){
				var r = this.scroll.call(this,arguments[0] === undefined?undefined:{left:arguments[0]});
				if(jBud.isBudObject(r)) return this;
				return r.left;
			},
			/**
			 * 上滚动宽度
			 */
			scrollTop:function(){
				var r = this.scroll.call(this,arguments[0] === undefined?undefined:{top:arguments[0]});
				if(jBud.isBudObject(r)) return this;
				return r.top;
			},
			/**
			 * 偏移量，相对body
			 */
			offset:function() {
				var set = arguments[0],jstyle = jBud.style;
				if(set === undefined) {
					if(this.length<=0) return undefined;
					return jstyle.offset(this[0]);
				}
				if(typeof set !== 'object') return this;
				set = jBud.extend({left:undefined,top:undefined},set);
				return this.each(function(index) {
					jstyle.setOffset(this,set,index);
				});
			},
			/**
			 * 偏移量，相对offsetParent
			 */
			position:function(){
				var jstyle = jBud.style;
				if(this.length<=0) return undefined;
				return jstyle.position(this[0]);
			},
			/**
			 * 样式设置和提取
			 */
			css:function(name,value){
				if(arguments.length <= 0) return this;
				if(typeof name === 'string' || jBud.isArray(name)) {
					//#006 解决CSS方法中，对于value=0的情况不处理的问题
					if(typeof value !== 'undefined' && typeof name === 'string') {
						return this.each(function(index){
							jBud.style.set(this,name,typeof value === 'function' ? value.call(this,index,jBud.style.get(this,name)) : value);
						});
					}
					if(!this[0]) return undefined;
					return jBud.style.get(this[0],name);
				} else if(jBud.isPlainObject(name)) {
					return this.each(function(index){
						for(var k in name){
							jBud.style.set(this,k,name[k]);
						}
					});
				}
			},
			/*#CSS控制 end #*/
			/*#DOM结构 start#*/
			/**
			 * 获取当前jBud容器所包含的文本，如果包含多个DOM对象，那么返回这些文本的叠加文本
			 * @return {String} 文本
			 */ 
			text:function(value) {
				var dom = jBud.dom;
				if(typeof value !== 'undefined') {
					return this.each(function(index){
						var children = this.childNodes,node,t;
						dom.empty(this);
						if(typeof value === 'function') t = value(index,jBud.text(this));
						// #011 解决对非方法的HTML进行构建的问题
						else if (value === null) t = '';
						else t = value.toString();
						node = document.createTextNode(t),this.appendChild(node);
					});
				} else {
					var ts = [];
					this.each(function(){
						ts.push(jBud.text(this));
					});
					return ts.join("");
				}
			},
			/**
			 * 设置或者获得DOM中的HTML内容
			 */
			html:function(value){
				var dom = jBud.dom;
				if(typeof value !== 'undefined') {
					return this.each(function(index){
						var oh = this.innerHTML,h;
						// #010 解决对非方法的HTML进行构建的问题
						if(typeof value === 'function') h = value(index,oh);
						else if (value === null) h = '';
						else h = value.toString();
						if(h === undefined || h === false) return true;
						dom.empty(this);
						if(typeof h !== 'string') return true;
						//#007 解决无法正确追加文本的问题
						jBud(this).append(dom.memory(h));
					});
				} 
				if(!this[0]) return undefined;
				return this[0].innerHTML;
			},
			_domControl:function(args,callback){
				var params = args,dom = jBud.dom,length,stopClone;
				if(params.length <= 0) return this;
				var fn = params[0];
				if(typeof fn === 'function') {
					return this.each(function(index){
						var cb = fn(index,this.innerHTML);
						if(cb === false || cb === undefined) return true;
						jBud(this)._domControl([cb],callback);
					});
				}
				stopClone = this.length-1;
				return this.each(function(index){
					//#005 解决在IE中无法使用DOM控制，原因由于IE下arguments无法使用foreach方式
					for(var k = 0;k<params.length;k++) {
						dom.control(this,params[k],index,stopClone,callback);
					}
				});
			},
			/**
			 * 追加DOM
			 */
			append:function() {
				return this._domControl(arguments,function(elem){
					this.appendChild(elem);
				});
			},
			appendTo:function(target) {
				jBud(target).append(this);
				return this;
			},
			/**
			 * 第一位插入
			 */
			prepend:function(){
				return this._domControl(arguments,function(elem){
					this.insertBefore(elem,this.firstChild);
				});
			},
			prependTo:function(target){jBud(target).prepend(this);return this;},
			empty:function(){
				return this.each(function(){jBud.dom.empty(this);});
			},
			/**
			 * 向后插入
			 */
			after:function(){
				return this._domControl(arguments,function(elem){
					if ( this.parentNode ) {
						this.parentNode.insertBefore( elem, this.nextSibling );
					}
				});
			},
			insertAfter:function(target){jBud(target).after(this);return this;},
			/**
			 * 向前掺入
			 */
			before:function(){
				return this._domControl(arguments,function(elem){
					if ( this.parentNode ) {
						this.parentNode.insertBefore( elem, this );
					}
				});
			},
			insertBefore:function(target){jBud(target).before(this);return this;},
			clone:function(){
				var clones = [];
				this.each(function(){
					clones.push(jBud.dom.clone(this));
				});
				return jBud(clones);
			},
			remove:function(selector){
				var dom = jBud.dom,subs = jBud(selector),parentNode;
				return this.each(function(){
					parentNode = this;
					if(selector === undefined) {
						parentNode = this.parentNode;
						if(parentNode && this)	parentNode.removeChild(this);
						return true;
					}
					subs.each(function(){
						if(jBud.contains(parentNode,this))
						parentNode.removeChild(this);
					});
				});
			},
			wrapAll:function(html){
				if(this.length <= 0) return this;
				var type = typeof html,first = this[0],parentNode=first.parentNode,wdom;
				if(!parentNode) return this;
				wdom = jBud(html);
				if(wdom.length <=0) return this;
				wdom = wdom[0];
				if(wdom.nodeType !== 1) return this;
				parentNode.insertBefore(wdom,first);
				jBud(wdom).append(this);
				return this;
			},
			wrap:function(html) {
				var type = typeof html,dom = jBud.dom,wdom;
				if(type === 'function') return this.each(function(index){
					jBud(this).wrap(jBud(html.call(this,index)));
				});
				wdom = jBud(html);
				if(wdom.length <=0) return this;
				wdom = wdom[0];
				return this.each(function(){
					var tdom = dom.clone(wdom);
					jBud(this).wrapAll(tdom);
				});
			},
			unwrap:function(){
				var dom = jBud.dom;
				return this.each(function(){
					var parentNode =this.parentNode;
					if(!parentNode || dom.nodeName(parentNode,'body')) return true;
					jBud(jBud.merge([],parentNode.childNodes)).insertBefore(parentNode);
					jBud(parentNode).remove();
				});
			},
			wrapInner:function(html){
				if(typeof html === 'function') return this.each(function(index){
					jBud(this).wrapInner(jBud(html.call(this,index)));
				});
				return this.each(function(){
					var self = jBud( this ),
						contents = self.contents();
					if ( contents.length ) {
						contents.wrapAll( html );
					} else {
						self.append( html );
					}
				});
			},
			contents:function(){
				var cs = [],dom = jBud.dom;
				this.each(function() {
					var node = dom.nodeName(this,'iframe') ? this.contentDocument || this.contentWindow.document : this.childNodes;
					jBud.merge(cs,node);
				});
				return jBud(cs);
			},
			replace:function(froms){
				if(typeof froms === 'function') return this.each(function(index){
					jBud(this).insertBefore(jBud(froms.call(this,index)));
				});
				jBud(froms).insertBefore(this);
				this.remove();
				return this;
			},
			replaceTo:function(target){jBud(target).replace(this);return this;},
			swap:function(froms){
				if(typeof froms === 'function') return this.each(function(index){
					jBud(this).swap(jBud(froms.call(this,index)));
				});
				var p = jBud(froms),tmp,swapClass;
				swapClass = jBud.uuid();
				p.before("<div class='"+swapClass+"'></div>");
				this.before(p);
				jBud("."+swapClass).replace(this);
				return this;
			},
			swapTo:function(target){
				jBud(target).swap(this);return this;
			},
			filter:function(selector,not,is){
				var type = typeof selector,find = jBud.find,dom = jBud.dom,self = this,matches,not = !!not,is = !!is,callback;
				if(arguments.length <= 0) return jBud([]);
				matches = [];
				this.each(function(index) {
					if(type === 'string' && (not ? !find.matchesSelector(this,selector) : find.matchesSelector(this,selector))) {
						matches.push(this);
						if(is) return true;
					} else if (jBud.isBudObject(selector)) {
						var p = this,result = false;
						selector.each(function(){
							if(p === this){ result = true; return false;}
						});
						if(not ? !result : result) { matches.push(this);if(is) return true;}
					} else if (dom.isElement(selector) && (not ? this !== selector : this===selector)){
						matches.push(this);
						if(is) return true;
					} else if (type === 'function' && (not ? !selector.call(this,index) : selector.call(this,index))) {
						matches.push(this);
						if(is) return true;
					} 
				});
				return jBud(matches);
			},
			_filterControl:function(selector,callback,one,until){
				var find = jBud.find,childs = [],list;
				if(this.length <= 0) return jBud(childs);
				this.each(function(index) {
					var r = callback.call(this);
					if(jBud.isArray(r)) {
						if(until) {
							for(var k = 0;k<r.length;k++) {
								if((jBud.dom.isElement(until) && r[k] === until) || (typeof until === 'string' && find.matchesSelector(r[k],until))) {
									r.splice(k,r.length);
									break;
								}
							}
						}
						childs = childs.concat(r);
					}
				});
				if(typeof selector === 'string') childs =find.matches(selector,childs);
				return jBud(childs);
			},
			children:function(selector){
				return this._filterControl(selector,function(){
					return jBud.dom.siblings(this);
				},false);
			},
			next:function(selector){
				return this._filterControl(selector,function(){
					return jBud.dom.siblings(this,this,true,true);
				},true);
			},
			nextAll:function(selector){
				return this._filterControl(selector,function(){
					return jBud.dom.siblings(this,this);
				},false);
			},
			nextUntil:function(until,selector){
				return this._filterControl(selector,function(){
					return jBud.dom.siblings(this,this);
				},false,until);
			},
			prev:function(selector){
				return this._filterControl(selector,function(){
					return jBud.dom.siblings(this,this,false,true);
				},true);
			},
			prevAll:function(selector){
				return this._filterControl(selector,function(){
					return jBud.dom.siblings(this,this,false);
				},false);
			},
			prevUntil:function(until,selector){
				return this._filterControl(selector,function(){
					return jBud.dom.siblings(this,this,false);
				},false,until);
			},
			siblings:function(selector){
				return this._filterControl(selector,function(){
					return jBud.dom.siblings(this,this,true).concat(jBud.dom.siblings(this,this,false));
				},false);
			},
			parent:function(selector){
				return this._filterControl(selector,function(){
					return jBud.dom.parents(this,true);
				},true);
			},
			parents:function(selector){
				return this._filterControl(selector,function(){
					return jBud.dom.parents(this,false); 
				},false);
			},
			parentUntil:function(until,selector){
				return this._filterControl(selector,function(){
					return jBud.dom.parents(this,false);
				},false,until);
			},
			offsetParent:function(){
				return this._filterControl(undefined,function(){
					return [jBud.style.offsetParent(this)];
				},false);
			},
			eq:function(index){
				var matches = [],self = this;
				if(typeof index !== 'number') return this;
				this.each(function(i){
					if (index >= 0 ? i === index : i === index+self.length) {
						matches.push(this);
					}
				});
				return jBud(matches);
			},
			first:function(){
				return this.eq(0);
			},
			last:function(){
				return this.eq(-1);
			},
			slice:function(start,end){
				var matches = [],ts = typeof start,te = typeof end;
				if(ts !== 'number') return this;
				if(te !== 'number') end = this.length;
				this.each(function(index){
					if(index >= start && index < end) matches.push(this);
				});
				return jBud(matches);
			},
			not:function(selector){
				return this.filter(selector,true);
			},
			is:function(selector){
				return this.filter(selector,false,true).length > 0;
			},
			isNot:function(selector){
				return !this.is(selector);
			},
			has:function(selector){
				var list = this.find("*"),matches = [];
				list.each(function(){
					if(jBud(this).is(selector)) matches.push(this);
				});
				list = null;
				return jBud(matches);
			},
			index : function(selector,all) {
				var dom = this[0] , result = -1, all;
				if(!dom) return result;
				if(jBud.isBoolean(selector)) {
					all = selector;
					selector = undefined;
				}
				if(typeof selector === 'undefined') {
					selector = this[0].parentNode;
				}
				jBud(selector).children().each(function(index) {
					if(!all && jBud(this).css("display") != 'none') {
						result++;
						if(this === dom) {
							return false;
						}
					} else {
						if(this === dom) {
							result = index;
							return false;
						}
					}
					
				});
				return result;
			},
			/*#DOM结构 end#*/
			/*#DOM属性 start#*/
			attr:function(name,value){
				var tn = typeof name,tv = typeof value;
				if(tv === 'undefined' && tn === 'string') {
					if(!this[0]) return undefined;
					return this[0].getAttribute(name);
				}
				return this.each(function(index){
					if(tn === 'string') {
						if(tv === 'function') {
							this.setAttribute(name,value.call(this,index,this.getAttribute(name)));
						} else {
							this.setAttribute(name,value);
						}
					} else if (jBud.isPlainObject(name)) {
						for(var k in name){
							this.setAttribute(k,name[k]);
						}
					}
				});
			},
			removeAttr:function(name) {
				var args = arguments;
				if(args.length <=0) return this;
				return this.each(function(){
					for(var k in args) {
						if(typeof args[k] === 'string') this.removeAttribute(args[k]);
					}
				});
			},
			prop:function(name,value){
				var tn = typeof name,tv = typeof value;
				if(tv === 'undefined' && tn === 'string') {
					if(!this[0]) return undefined;
					return this[0][name];
				}
				return this.each(function(index){
					if(tn === 'string') {
						if(tv === 'function') {
							this[name] = value.call(this,index,this[name]);
						} else {
							this[name] = value;
						}
					} else if (jBud.isPlainObject(name)) {
						for(var k in name){
							this[k] = name[k];
						}
					}
				});
			},
			removeProp:function(){
				var args = arguments;
				if(args.length <=0) return this;
				return this.each(function(){
					for(var k in args) {
						if(typeof args[k] === 'string') {
							 this[args[k]] = undefined;
						}
					}
				});
			},
			val:function(value){
				var valEx = jBud.valExtend,type = typeof value;
				if(type === 'undefined') {
					var dom = this[0],bud,key;
					if(!dom) return undefined;
					key = dom.nodeName.toLowerCase();
					return valEx[key] && valEx[key].get ? valEx[key].get(dom):dom.value;
				} 
				return this.each(function(index){
					var key = this.nodeName.toLowerCase(),v;
					if(type === 'function') v = value.call(this,index,jBud(this).val());
					else v = value;
					valEx[key] && valEx[key].set?valEx[key].set(this,v) : (this.value = v);
				});
			}
			/*#DOM属性 end#*/
	};
	
	/*#QUEUE COMPONENT START#*/
	jBud.queue = {
			defName:'__queue__',
			get:function(elem,name){
				var bud,links;
				if(typeof name === 'undefined') name = this.defName;
				bud = jBud.bud(elem),queues = bud.queues;
				if(!queues) queues = bud.queues = {};
				if(!(links = queues[name]) || !(links instanceof Links)) links = queues[name]  = new Links(elem);
				return links;
			},
			set:function(elem,name,commands){
				var links = this.get(elem,name);
				links.enter(commands);
				return links;
			},
			run:function(obj,name,force){
				var links = undefined;
				if(obj instanceof Links) links = obj;
				else if(jBud.dom.isElement(obj)) links = this.get(obj,name);
				else return links;
				links.go(force);
				return links;
			},
			clear:function(obj,name){
				var links = undefined;
				if(obj instanceof Links) links = obj;
				else if(jBud.dom.isElement(obj)) links = this.get(obj,name);
				else return links;
				links.clear();
				return links;
			}
	};
	jBud.extend(jBud.seed,{
		/*#queue start#*/
		/**
		 * 入队
		 */
		queue:function(name,commands){
			var tn = typeof name,tc = typeof commands,len = arguments.length,bud,queues,links;
			if(len <= 1 && (tn === 'undefined' || tn === 'string')) {
				if(!this[0]) return undefined;
				return jBud.queue.get(this[0],name);
			}
			if(tn === 'function' || jBud.isArray(name)) {commands = name;name = undefined;}
			return this.each(function(){
				links = jBud.queue.set(this,name,commands);
				jBud.queue.run(links);
			});
		},
		/**
		 * 出队
		 */
		dequeue:function(name){
			return this.each(function() {
				jBud.queue.run(this,name,true);
			});
		},
		/**
		 * 清队
		 */
		clearQueue:function(name){
			return this.each(function(){
				jBud.queue.clear(this,name);
			});
		},
		/**
		 * 延迟
		 */
		delay:function(duration,name){
			if(!jBud.isNumeric(duration)) return this;
			return this.queue(name,function(next){
				var timer;
				timer = window.setTimeout(function(){next();window.clearTimeout(timer);timer = undefined;},duration);
			});
		}
		/*#queue end#*/
	});
	/*#QUEUE COMPONENT END#*/
	
	/*#PERFORM START#*/
	jBud.action = {
			interval:1000/60,
			duration:400,
			blocks:["width","height"],
			position:["Top","Right","Bottom","Left"],
			prop:{
				__handle__:function(prefix,suffix,actor,ps,value){
					var pos=jBud.action.position;
					for(var k in pos){
						var kk = prefix+pos[k]+suffix,v;
						v = typeof value !== 'undefined' ? value : parseFloat(actor.css(kk));
						ps[kk] = isNaN(v) ? 0 : v;
					}
					delete ps[prefix+suffix];
				},
				borderWidth:function(actor,ps,value){
					return jBud.action.prop.__handle__("border","Width",actor,ps,value);
				},
				padding:function(actor,ps,value){
					return jBud.action.prop.__handle__("padding","",actor,ps,value);
				},
				margin:function(actor,ps,value){
					return jBud.action.prop.__handle__("margin","",actor,ps,value);
				}
			},
			easing : {
				easeinout:function(time, begin, change, duration){
					return jBud.action.easing.swing(time, begin, change, duration);
				},
				swing:function(time, begin, change, duration){
					if ((time /= duration / 2) < 1) {
				      return change/2 * time * time + begin;
				    } else {
				      return -change/2 * ((--time) * (time - 2) - 1) + begin;
				    }
				},
				linear:function(time,begin,change,duration){
					return change * time/duration + begin;
				}
			}
	};
	
	var Perform = function(actor,properties,options){
		this.properties = {};
		this.beginValue = {};
		this.options = {
				duration:jBud.action.duration,
				easing:'easeinout',
				begin:function(){},
				complete:function(){}
		};
		//表演者
		this.actor = jBud(actor);
		jBud.extend(this.properties,properties);
		jBud.extend(this.options,options);
		this.timer = undefined;
		this.startTime = undefined;
		this.doneFunc = function(){};
		this.isMake=false;
		this.isDone = false;
	};
	jBud.extend(Perform.prototype,{
		//读取初始值
		makeBeginValue:function() {
			var prop = jBud.action.prop,bv = this.beginValue,v,isBlock;
			for(k in this.properties) {
				v = parseFloat(this.actor.css(k));
				v = isNaN(v) ? 0 : v;
				if(prop[k]) {
					prop[k](this.actor,this.properties,this.properties[k]);
					prop[k](this.actor,this.beginValue);
				} else {
					bv[k] = v;
				}
				if(jBud.inArray(k.toLowerCase(),jBud.action.blocks) >= 0) isBlock = true;
			}
			if(isBlock) {
				var display = this.actor.css("display");
				if(display === 'inline')
				this.actor.css("display","inline-block");
			}
			this.isMake = true;
		},
		//准备
		action:function(){
			if(this.timer || this.isDone) {
				this.done();
				return this;
			}
			var opt = this.options;
			var self = this;
			this.makeBeginValue();
			this.startTime = new Date().getTime();
			this.timer = setInterval(function(){self.step();},jBud.action.interval);
			opt.begin();
		},
		//执行表演
		step:function() {
			var opt = this.options,easing = jBud.action.easing,ease = easing[opt.easing],time = (new Date().getTime()) - this.startTime;
			if(typeof ease === 'function') {
				for(var k in this.properties) {
					var begin = parseFloat(this.beginValue[k]),target = parseFloat(this.properties[k]),change = target - begin,value;
					value = ease(time,begin,change,opt.duration);
					this.actor.css(k,value+"px");
				}
			}
	        if (time > opt.duration) {
	        	this.end();
	        }
		},
		setDone:function(done){
			if(typeof done === 'function') this.doneFunc = done;
		},
		interrupt:function(){
			if(this.timer) clearInterval(this.timer);
			this.timer = null;
		},
		end:function(){
			this.interrupt();
			if(!this.isMake) this.makeBeginValue();
        	for(k in this.properties) {
        		this.actor.css(k,this.properties[k]+"px");
        	}
        	this.options.complete();
        	this.doneFunc();
        	this.isDone = true;
		},
		done:function(){
			this.doneFunc();
		}
	});
	
	jBud.extend(jBud.seed,{
		//动画队列
		action:function(props,options){
			if(arguments.length <= 0) return this;
			var opts = {queue:true};
			jBud.extend(opts,options);
			return this.each(function(){
				var perform = new Perform(this,props,opts);
				var fn = function(next){
					perform.setDone(function(){
						if(typeof next === 'function') next();
					});
					return perform.action();
				};
				fn.$$perform = perform;
				jBud(this).queue(fn);
				if(!opts.queue) {
					perform.action();
				}
			});
		},
		//兼容jQuery
		animate:function(){
			return this.action.apply(this,arguments);
		},
		//终止
		cut:function(clear,end){
			return this.each(function(){
				var $this = jBud(this),actions = $this.queue(),first,perform;
				if(actions && (first = actions.getCurrent()) && (perform = first["$$perform"]) && (perform instanceof Perform)){
					perform.interrupt();
				}
				if(actions && actions.currentIterator) {
					//遍历当前正在运行的队列
					actions.currentIterator(function(node){
						if(node instanceof Perform) {
							//终止运行
							node.interrupt();
							//如果是end，那么直接执行end操作
							if(end) node.end();
						}
					});
				}
				if(clear) $this.clearQueue();
				if(end && perform) perform.end();
				if(perform) perform.done();
			});
		},
		//兼容jQuery
		stop:function(){return this.cut.apply(this,arguments);},
		//是否在播放中
		isPlaying:function(){
			if(!this[0]) return true;
			var actions = jBud(this[0]).queue();
			return actions.queue.length <= 0;
		},
		show : function(time) {
			if(!jBud.isNumeric(time)) time = undefined;
			return this.each(function() {
				var $this = jBud(this),width,height;
				if(typeof time === 'undefined') {
					$this.css("display","block");
				} else {
					$this.css("display","block");
					width = $this.width(),height = $this.height();
					$this.width("0px").height("0px");
					$this.action({
						width:width,
						height:height
					},{
						duration:time
					});
				}
			});
		},
		hide : function(time) {
			if(!jBud.isNumeric(time)) time = undefined;
			return this.each(function() {
				var $this = jBud(this),width,height;
				if(typeof time === 'undefined') {
					$this.css("display","none");
				} else {
					$this.action({
						width:0,
						height:0
					},{
						duration:time,
						complete:function(){$this.css("display","none");}
					});
				}
			});
		},
		fadeIn : function(time,callback) {
			var self = this;
			if(jBud.isFunction(time)) {
				callback = time;
				time =  jBud.action.duration;
			} 
			if(!jBud.isNumeric(time)) time =  jBud.action.duration;
			this.css("opacity",0);
			this.show();
			
			return this.action({
				opacity:1
			},{
				duration:time,
				complete : function(){
					if(callback) callback();
				}
			});
		},
		fadeOut : function(time,callback) {
			var self = this;
			
			if(jBud.isFunction(time)) {
				callback = time;
				time =  jBud.action.duration;
			}
			if(!jBud.isNumeric(time)) time =  jBud.action.duration;
			this.css("opactiy",1);
			this.show();
			return this.action({
				opacity:0
			},{
				duration:time,
				complete : function(){
					if(callback) callback();
				}
			});
		}
	});
	/*#PERFORM END#*/
	
	/*#AJAX START#*/
	jBud.XMLHttp = {
			config:{
				async: true,
				type:'GET',
				contentType: "application/x-www-form-urlencoded; charset=UTF-8",
				//accept:"text/javascript, application/javascript, application/ecmascript, application/x-ecmascript, */*; q=0.01",
				accpet:"*/*",
				dataType:'auto',
				username:undefined,
				password:undefined,
				cache:false,
				jsonp:'callback',
				jsonpCallback:undefined,
				timeout:-1,
				charset:'UTF-8',
				data:undefined,
				beforeSend:function(){},
				success:function(){},
				error:function(){},
				complete:function(){}
			},
			request:function() {
				var req = undefined;
				if(window.XMLHttpRequest) {
					req = new XMLHttpRequest();
				} else if(window.ActiveXObject){
					try{
						req = new ActiveXObject("Microsoft.XMLHTTP");
					}catch(e) {}
				} 
				return req;
			},
			service:function(request,options) {
				if(!request) return false;
				var config = jBud.XMLHttp.config,self = this,opts = jBud.extend({},config),url,isAbort,links;
				links = jBud.Links();
				jBud.extend(opts,options);
				opts.success = jBud.assign(opts.success,config.success);
				opts.error = jBud.assign(opts.error,config.error);
				opts.complete = jBud.assign(opts.complete,config.complete);
				opts.beforeSend = jBud.assign(opts.beforeSend,config.beforeSend);
				request.onreadystatechange = function() {
					if(request.readyState == 4) {
						if(request.status == 200) {
							var result=self.convert(request,opts.dataType);
							opts.success(result,request.statusText,request);
							links.attack(result,request.statusText,request);
						} else {
							opts.error(isAbort?"timeout":request.statusText,request);
							links.retreat(undefined,request.statusText,request);
						}
						opts.complete(request.statusText,request);
					}
				};
				if(!opts.type || typeof opts.type !== 'string') opts.type = "GET";
				opts.type = jBud.trim(opts.type.toUpperCase());
				url = opts.url;
				if(opts.type === 'GET') {
					var query = url.indexOf("?"),ps = this.serialize(opts.data);
					url += (query >= 0 ? "&":"?")+ps;
					if(!opts.cache) url += "&"+(new Date().getTime())+Math.floor(Math.random()*9999);
				}
				try{
					if(opts.username)
						request.open(opts.type,url,opts.async,opts.username,opts.password);
					else 
						request.open(opts.type,url,opts.async);
				} catch(e) {
					opts.error(e.message,request);
					links.retreat(undefined,e.message,request);
					return links;
				}
				if(!opts.cache) {
					request.setRequestHeader("If-Modified-Since","0");
					request.setRequestHeader("Cache-Control","no-cache");
					request.setRequestHeader("Pragma","no-cache");
				}
				request.setRequestHeader("Content-Type",config.contentType);
				request.setRequestHeader("Accept","*/*");
				//通知服务器使用 X-Request-With ，表明AJAX请求
				request.setRequestHeader("X-Requested-With","XMLHttpRequest");
				opts.beforeSend(request);
				if(opts.type === 'POST') {
					request.send(this.serialize(opts.data));
				} else {
					request.send(null);
				}
				if(opts.async && opts.timeout > 0) {
					setTimeout(function(){
						isAbort = true;
						request.abort("timeout");
					},opts.timeout);
				}
				return links;
			},
			//跨域中的JSONP形式构建
			jsonp:function(options){
				var config = jBud.XMLHttp.config,self = this,opts = jBud.extend({},config),callbackKey,callbackName,url,query,exist,ps,links;
				jBud.extend(opts,options);
				opts.success = jBud.assign(opts.success,config.success);
				opts.error = jBud.assign(opts.error,config.error);
				opts.complete = jBud.assign(opts.complete,config.complete);
				opts.beforeSend = jBud.assign(opts.beforeSend,config.beforeSend);
				callbackKey = opts.jsonp,callbackName = opts.jsonpCallback,url = opts.url,query = url.indexOf("?");
				links = jBud.Links();
				if(typeof callbackName === 'undefined') {
					callbackName = "jBud"+(new Date().getTime())+"_"+Math.floor(Math.random()*99999);
				}
				ps = this.serialize(opts.data);
				url += (query >= 0 ? "&":"?")+callbackKey+"="+callbackName;
				if(ps.length > 0) url += "&"+ps;
				exist = !!window[callbackName];
				if(!exist) {
					window[callbackName] = function(){
						opts.success.apply(null,arguments);
						links.attack.apply(links,arguments);
						try{
							delete window[callbackName];
						} catch(e) {
							window[callbackName] = undefined;
						}
					};
				}
				var script = document.createElement("script"),head = document.getElementsByTagName("head")[0] || document.documentElement;
				script.type = "text/javascript";
				script.src = url;
				script.async = opts.async;
				if(opts.charset) script.charset = opts.charset;
				script.onload = script.onreadystatechange = function(_, abort ) {
					if ( abort || !script.readyState || /loaded|complete/.test( script.readyState ) ) {
						script.onload = script.onreadystatechange = null;
						if ( script.parentNode ) {
							script.parentNode.removeChild( script );
						}
						script = null;
						opts.complete();
						if(abort) {
							opts.error("timeout");
							links.retreat.call(links,undefined,"timeout");
							if(!exist) {
								window[callbackName] = function(){
									try{
										delete window[callbackName];
									}catch(e) {
										window[callbackName] = undefined;
									}
								};
							}
						}
					}
				};
				opts.beforeSend();
				head.insertBefore( script, head.firstChild );
				if(opts.timeout > 0) {
					setTimeout(function(){
						if(script) script.onload( undefined, true );
					},opts.timeout);
				}
				return links;
			},
			getScript:function(options){
				var opts = jBud.extend({
					url:undefined,async:false,charset:'UTF-8',
					cache:true,complete:function(){},remove:false,last:true,id:undefined
				},options),url = opts.url;
				opts.complete = jBud.assign(opts.complete,function(){});
				if(!opts.cache) {
					var query = url.indexOf("?");
					url += (query > 0 ? "&":"?")+(new Date().getTime())+"=1";
				}
				var script = document.createElement("script"),head = document.getElementsByTagName("head")[0];
				script.type = "text/javascript";
				script.src = url;
				script.async = opts.async;
				if(typeof opts.id === 'string') script.id = opts.id;
				if(opts.charset) script.charset = opts.charset;
				script.onload = function(){
					opts.complete();
				};
				script.onreadystatechange = function(){
					if(/loaded|complete/.test( script.readyState )){
						script.onreadystatechange = null;
						opts.complete();
					}
				};
				script.onerror = function() {
					opts.complete();
				};
				if(opts.last)
					head.appendChild(script);
				else 
					head.insertBefore( script, head.firstChild );
			},
			//序列化
			serialize:function(data,encode){
				if(typeof data === 'undefined' || data === null) return '';
				if(jBud.isArray(data) || !jBud.isPlainObject(data)){return data.toString();}
				var v = [],xmlhttp = jBud.XMLHttp;
				for(k in data) {
					var d = data[k];
					if(jBud.isArray(d)) {
						for(var i =0;i<d.length;i++){
							var it = d[i];
							it = (typeof it === 'undefined' || it === null) ? '' : it;
							v.push(encodeURIComponent(k)+"="+encodeURIComponent(it));
						}
						continue;
					} 
					if(jBud.isPlainObject(d)) {
						v.push(xmlhttp.serialize(d));
					} else{
						d = (typeof d === 'undefined' || d === null) ? '' : d;
						v.push(encodeURIComponent(k)+'='+encodeURIComponent(d.toString()));
					}
				}
				var r = v.join("&");
				v = null;
				return encode ? encodeURI(r) : r;
			},
			//转化
			convert:function(request,type){
				if(!request) return undefined;
				if(!type || typeof type !== 'string') type = 'auto';
				type = jBud.trim(type.toLowerCase());
				var exec = undefined;
				if((exec = this.parse[type]) && typeof exec === 'function') {
					return exec(request);
				}
				return request.responseText;
			},
			//转换
			parse:{
				_type_:["xml","json","html","text"],
				"auto":function(request){
					var ct = request.getResponseHeader("Content-Type"),parse = jBud.XMLHttp.parse,types=parse._type_;
					for(var k in types) {
						var reg = new RegExp("\\b"+types[k]+"\\b","ig");
						if(reg.test(ct)) {
							return parse[types[k]](request);
							break;
						}
					}
					return request.responseText;
				},
				"xml":function(request){
					return jBud.XMLHttp.parseXML(request.responseXML);
				},
				"json":function(request){
					var text = request.responseText;
					return jBud.XMLHttp.parseJSON(text);
				},
				"html":function(request){return request.responseText;},
				"text":function(request){return request.responseText;}
			},
			//转换JSON
			parseJSON:function(text){
				if ( window.JSON && window.JSON.parse ) {
					try {
						return window.JSON.parse( text );
					} catch(e){
						throw new Error("parse json error");
					}
				}
				if ( text === null ) {
					return text;
				}
				if ( typeof text === "string" ) {
					text = jBud.trim(text);
					if (text) {
						return ( new Function( "return " + text ) )();
					}
				}
				throw new Error("parse json error");
			},
			//转换XML
			parseXML:function(data){
				var xml, tmp;
				if(typeof data === 'object') return data;
				if ( !data || typeof data !== "string" ) {
					return null;
				}
				try {
					if ( window.DOMParser ) {
						tmp = new DOMParser();
						xml = tmp.parseFromString( data , "text/xml" );
					} else { 
						xml = new ActiveXObject( "Microsoft.XMLDOM" );
						xml.async = "false";
						xml.loadXML( data );
					}
				} catch( e ) {
					xml = undefined;
				}
				if ( !xml || !xml.documentElement || xml.getElementsByTagName( "parsererror" ).length ) {
					throw new Error("parse xml error");
				}
				return xml;
			}
	};
	jBud.extend({
		assign:function(source,def){
			if(typeof source !== typeof def) return def;
			return source;
		},
		ajax:function(options){
			var type = options.dataType,xhr;
			if(!type || typeof type !== 'string') type = 'auto';
			type = jBud.trim(type.toLowerCase());
			if(type === 'jsonp') 
				return jBud.XMLHttp.jsonp(options);
			else {
				if(!(xhr = jBud.XMLHttp.request())) return undefined;
				return jBud.XMLHttp.service(xhr,options);
			}
		},
		request:function(url,data,callback,dataType,type) {
			if(jBud.isPlainObject(url)) {
				return this.ajax(url);
			}
			if (jBud.isFunction( data ) ) {
				type = type || dataType || callback;
				dataType = dataType || callback;
				callback = data;
				data = undefined;
			}
			if(!type) type = "GET";
			return this.ajax({
				url:url,data:data,success:callback,dataType:dataType,type:type
			});
		},
		jsonp:function(url,data,callback){
			if(jBud.isPlainObject(url)) {
				url.dataType = 'jsonp';
			}
			return this.request(url,data,callback,'jsonp',"GET");
		},
		post:function(url,data,callback,dataType){
			return this.request(url,data,callback,dataType,"POST");
		},
		getJSON:function(url,data,callback){
			return this.request(url,data,callback,"json","GET");
		},
		getXML:function(url,data,callback){
			return this.request(url,data,callback,'xml','GET');
		},
		get:function(url,data,callback,dataType){
			return this.request(url,data,callback,dataType,"GET");
		},
		parseJSON:function(data){return jBud.XMLHttp.parseJSON(data);},
		parseXML:function(data){return jBud.XMLHttp.parseXML(data);},
		serialize:function(data,encode){return jBud.XMLHttp.serialize(data,encode);},
		getScript:function(url,callback){
			if(jBud.isPlainObject(url)) {
				return jBud.XMLHttp.getScript(url);
			}
			return jBud.XMLHttp.getScript({
				url:url,complete:callback
			});
		},
		_KV_:function(reg,text){
			var temp, ps = {};
			while ((temp = reg.exec(text)) != null) {
				ps[temp[1]] = decodeURIComponent(temp[2]);
			}
			return ps;
		},
		KV:function(text) {
			return this._KV_(/(?:&)?(.*?)=(.*?)(?=&|$)/g,text);
		},
		KVSearch:function(){
			return this._KV_(/(?:\?|&)(.*?)=(.*?)(?=&|$)/g,window.location.search);
		}
	});
	/*#AJAX END#*/
	
	jBud.seed.instance.prototype = jBud.seed;
	
	/*#LISTENER TEMPLATE START#*/
	var Listener = {
			__initQueue__:function(){
				if(!this.__queue__) this.__queue__ = {};
				return this.__queue__;
			},
			addEventListener:function(name,fn){
				this.__initQueue__();
				var listeners = this.__queue__[name];
				if(!listeners) listeners = this.__queue__[name] = [];
				if(typeof fn !== 'function') return;
				listeners.push(fn);
			},
			removeEventListener:function(name,fn){
				this.__initQueue__();
				var listeners = this.__queue__[name];
				if(!listeners || typeof fn !== 'function') return ;
				for(var i = listeners.length;i>=0;i--) {
					var listen = listeners[i];
					if(listen === fn) {
						delete listen;
					}
				}
			},
			emit:function(name,data){
				this.__initQueue__();
				var listeners = this.__queue__[name];
				if(!listeners) return ;
				for(var i = 0;i<listeners.length;i++){
					var listen = listeners[i];
					if(typeof listen !== 'function') continue;
					listen.call(this,data);
				}
			},
			removeEventListeners : function(callback) {
				this.__initQueue__();
				if(typeof callback === 'function') {
					var names = this.__queue__;
					for(var key in names) {
						var result = callback.call(this,key);
						if(result === true) {
							delete names[key];
						}
					}
				} else {
					delete this._queue_;
					this.__queue__ = {};
				}
			}
	};
	/**
	 * 启用监听器
	 */
	jBud.enableListener = function(target) {
		var type = typeof target;
		if(type === 'function') {
			jBud.extend(target.prototype,Listener);
		} else if (jBud.isPlainObject(target)) {
			jBud.extend(target,Listener);
		}
		return target;
	};
	/*#LISTENER TEMPLATE END#*/
	
	/*#CMD START#*/
	//Define Module Object
	var ModuleCache = {};
	var ModuleUtils = {
			_regexp_:{
				parent:/[^?#]*\//,
				dot:/\/\.\//g,
				double:/\/[^/]+\/\.\.\//,
				root:/^.*?\/\/.*?\//,
				absolute:/^\/\/.|:\//,
				slash:/\\\\/g,
				require:/"(?:\\"|[^"])*"|'(?:\\'|[^'])*'|\/\*[\S\s]*?\*\/|\/(?:\\\/|[^\/\r\n])+\/(?=[^\/])|\/\/.*|\.\s*require|(?:^|[^$])\brequire\s*\(\s*(["'])(.+?)\1\s*\)/g
			},
			/*
			 * 当前运行中的脚本
			 */
			current : function(last){
				var scripts = document.getElementsByTagName("script");
				if(scripts.length <= 0) return undefined;
				if(last) return scripts[scripts.length-1];
				return scripts[0];
			},
			/*
			 * 最前脚本
			 */
			first:function(){
				return this.current(false);
			},
			/*
			 * 最后脚本
			 */
			last:function(){
				return this.current(true);
			},
			parent:function(url){
				return url.match(this._regexp_.parent)[0];
			},
			absolute:function(script){
				return script.hasAttribute?script.src : script.getAttribute("src",4);
			},
			path:function(url){
				var query = url.indexOf("?");
				if(query >= 0) url = url.substring(0,query);
				return url;
			},
			realpath:function(url){
				url = url.replace(this._regexp_.dot, "/");
				while (url.match(this._regexp_.double)) {
					url = url.replace(this._regexp_.double, "/");
				}
				return url;
			},
			configpath:function(id,ref){
				var first = id.charAt(0),regexp = this._regexp_,base = config.base,ret;
				if (regexp.absolute.test(id)) {
					ret = id;
				} else if (first === ".") {
				    ret = this.realpath((ref ? this.parent(ref) : base) + id);
				} else if (first === "/") {
				    var m = base.match(regexp.root);
				    ret = m ? m[0] + id.substring(1) : id;
				}else {
				    ret = base + id;
				}
				return ret;
			},
			//正确的地址
			right:function(url) {
				var point,isDir,suffix,add,cache;
				point = url.lastIndexOf(".");
				if(point < 0) {
					add = true;
				} else {
					suffix = url.substring(point+1);
					if(!/^(js|css)$/ig.test(suffix)) {
						add = true;
					} else {
						isDir = suffix.indexOf("/");
						if(isDir >= 0) {
							add = true;
						}
					}
				}
				if(typeof config.timestamp === 'undefined') {
					cache = "";
				} else if(typeof config.timestamp === 'string'){
					cache = "?"+jBud.trim(config.timestamp)+"=1";
				} else if (jBud.isDate(config.timestamp)){
					cache = "?"+config.timestamp.getTime()+"=1";
				}
				return {
					id:url+(!!add?".js":""),
					uri:url+(!!add?(!!config.debug?"-debug.js":".js"):"")+cache
				};
			},
			get:function(id){
				return ModuleCache[id];
			},
			has:function(id){
				return !!ModuleCache[id];
			},
			hasListener:function(path){
				return !!ModuleQueue[path];
			},
			queue:function(path){
				var item = ModuleQueue[path];
				if(!item) {
					item = ModuleQueue[path] = {};
					jBud.enableListener(ModuleQueue[path]);
				}
				return item;
			},
			emit:function(path,name,data){
				var item = ModuleQueue[path];
				if(!item) return ;
				item.emit(name,data);
			}
	};
	
	//Module Object
	var Module = function() {
		//最终ID
		this.id = undefined;
		//绝对URI
		this.uri = undefined;
		//EXPORTS
		this.exports = {};
		//依赖
		this.depends = [];
		//原始ID
		this.sourceId = undefined;
		//已加载的脚本数量
		this.loaded = 0;
		//回调函数
		this.callback = undefined;
		//被使用与Use
		this.isBeUse = false;
		//相关索引
		this.ref = undefined;
		//状态
		this.state = "READY";
		//已加载的MAP
		this.map = {};
		this.realDepends = [];
	};
	Module.STATE = {
			READY:"READY",LOADING:"LOADING",LOADED:"LOADED",DEFINING:"DEFINING",DEFINED:"DEFINED"
	};
	jBud.extend(Module.prototype,{
		/**
		 * 获得ID，即绝对路径
		 */
		getId:function() {
			var script = ModuleUtils.last();
			if(!script) return undefined;
			return ModuleUtils.path(ModuleUtils.absolute(script));
		},
		/**
		 * 添加依赖，可以是字符串，或者数组
		 */
		pushDepends:function(depend){
			if(typeof depend === 'string') this.depends.push(depend);
			else if (jBud.isArray(depend)) this.depends = this.depends.concat(depend);
		},
		/**
		 * 加载主脚本
		 */
		load:function() {
			var self = this;
			if(this.isBeUse) {
				this.state = Module.STATE.LOADED;
				this.loadDepends();
			} else {
				var data = this.resolve(this.sourceId,this.ref);
				this.id = data.id,this.uri = data.uri;
				this.state = Module.STATE.READY;
				//预加载到缓存队列中
				this.pushModule();
				//开始执行加载
				jBud.getScript({
					url:this.uri,
					charset:config.charset,
					complete:function() {
						self.state = Module.STATE.LOADED;
					}
				});
				this.state = Module.STATE.LOADING;
			}
		},
		/**
		 * 加载依赖项
		 */
		loadDepends:function() {
			var ds = this.depends,self = this;
			if(!ds || ds.length<=0) {
				return this.exec();
			}
			for(var i = 0;i<ds.length;i++) {
				var d = ds[i],data = this.resolve(d,this.id),module;
				this.realDepends.push(data.id);
				if((module = ModuleUtils.get(data.id)) && module.state === Module.STATE.LOADED) {
					this.map[data.id] = true;
					continue;
				}
				if(!module) {
					module = new Module();
					module.sourceId = d;
					module.ref = this.uri;
				}
				module.addEventListener("define",function() {
					if(this.state === Module.STATE.DEFINED) {
						self.map[this.id] = true;
						if(self.isLoaded()) {
							self.exec();
							this.removeEventListener("define",arguments.callee);
						}
					}
				});
				if(module.state === Module.STATE.READY) module.load();
			}
			if(this.isLoaded()) {
				self.exec();
			}
		},
		isLoaded:function() {
			var ds = this.realDepends;
			for(var i = 0;i<ds.length;i++){
				if(!this.map[ds[i]]) return false;
			}
			return true;
		},
		/** 
		 * 执行define加载
		 */
		exec:function() {
			if(this.state !== Module.STATE.DEFINED) {
				if(this.callback)
					this.callback.call(jBud,this.require,this.exports,this);
				this.state = Module.STATE.DEFINED;
				this.emit("define");
			}
		},
		/**
		 * 解析ID
		 */
		resolve:function(id,ref) {
			return ModuleUtils.right(ModuleUtils.configpath(id,ref));
		},
		/**
		 * 获取缓存内容
		 */
		cache:function(){
			return ModuleCache;
		},
		/**
		 * 获取已缓存的模型
		 */
		require:function(id) {
			var mid = ModuleUtils.right(ModuleUtils.configpath(id)).id;
			return ModuleUtils.get(mid).exports;
		},
		/**
		 * 将模型推送到缓存中
		 */
		pushModule:function(){
			ModuleCache[this.id] = ModuleCache[this.id] || this;
		}
	});
	
	//为Module绑定监听事件
	jBud.extend(Module.prototype,Listener);
	//jBud.enableListener(Module.);
	
	//Define Config
	var selfScript = ModuleUtils.current(true),absolutePath = ModuleUtils.absolute(selfScript);
	var basedir = ModuleUtils.parent(absolutePath) || ModuleUtils.parent(window.location.href);
	
	//读取默认配置页
	var configPath = selfScript.getAttribute("data-config");
	if(configPath && typeof configPath === 'string' && (configPath = jBud.trim(configPath)).length > 0);
	//读取默认入口包
	var configMain = selfScript.getAttribute("data-main");
	if(configMain && typeof configMain === 'string' && (configMain = jBud.trim(configMain)).length > 0);
	var configCache = selfScript.getAttribute("data-cache");
	configCache = !!(!configCache ? true : configCache && configCache == 'true');
	
	var configParams = selfScript.getAttribute("data-params");
	configParams = typeof configParams !== 'string' ? '' : configParams;
	configParams = jBud.KV(configParams);
	jBud.getConfigParameters = function(){
		return configParams;
	};
	
	//异步读取配置
	var loadConfig = function(callback){
		if(configPath && configPath.length > 0) {
			jBud.getScript({
				url:configPath,
				cache:configCache,
				complete:function(){
					callback();
				}
			});
		}
	};
	
	//加载MAIN函数
	var loadMain = function() {
		if(configMain && configMain.length > 0) {
			var mains = configMain.split(",");
			jBud.use(mains);
		}
	};
	
	var config = {
			base:basedir,
			debug:false,
			timestamp:undefined,
			charset:"UTF-8"
	};
	
	jBud.config = function(options){
		jBud.extend(config,options);
	};
	
	// Define Custom Module
	// Compliance with CMD /  Modules/Transport 
	var define = jBud.define = function(id,depends,callback) {
		if(jBud.isArray(id)) {
			callback = depends || id, dpends = id , id = undefined;
		} else if (jBud.isFunction(id)) {
			callback = id, id = undefined, depends = [];
		} else if (typeof id === 'string') {
			if(jBud.isFunction(depends)) {
				callback = depends, depends = [];
			}
		}
		var data = ModuleUtils.right(ModuleUtils.configpath(id)),uri,module;
		uri = data.uri;
		module = ModuleUtils.get(data.id);
		//设定状态为正在定义中
		module.state = Module.STATE.DEFINING;
		module.pushDepends(depends);
		module.callback = callback;
		module.loadDepends();
		return jBud;
	};
	
	//Use Module
	var use = jBud.use = function(ids,callback) {
		//判断是否为字符串类型
		if(typeof ids === 'string') ids = [ids];
		//判断不为数组类型，如果是，那么返回
		if(!jBud.isArray(ids)) return jBud;
		var module = new Module();
		module.isBeUse = true;
		module.pushDepends(ids);
		module.callback = function(require,exports,module) {
			if(callback) {
				callback.call(jBud,require,exports,module);
			}
			delete module.callback;
		};
		//加载
		module.load();
	};
	//make define function attribute cmd is true , which means compliance with CMD 
	define.cmd = true;
	//default to load config path
	if(configPath && configPath.length > 0) {
		loadConfig(function(){
			if(loadMain) loadMain();
		});
	} else {
		loadMain();
	}
	/*#CMD END#*/
	
	/*# Links start #*/
	/**
	 * 链式处理规则
	 * Inspired by "Links zwo drei vier"
	 */
	var Links = function(commander,assert){
		//长官
		this.commander = commander;
		//命令队列
		this.cmds=[];
		//任务队列
		this.queue=[];
		//是否忽略
		this.assert = !!assert;
		this.length = 0;
		this.isGo = false;
		this.current = undefined;
		//正在运行的队列
		this.currentRun = [];
	};
	jBud.extend(Links.prototype,{
		/**
		 * 装载
		 */
		_install_:function(type,commands,always){
			if(!this.cmds) return this;
			always = !!always;
			var k =0;
			for(;k<commands.length;k++){
				if(typeof commands[k] === 'function') {
					switch(type) {
					case "queue":this.queue.push(commands[k]);break;
					default:this.cmds.push({type:type,cmd:commands[k],always:always});
					}
				} else if(jBud.isArray(commands[k])) {
					this._install_(type,commands[k],always);
				}
			}
			return this;
		},
		/**
		 * 胜利装载处理
		 */
		victory:function(){return this._install_("victory",arguments,false);},
		/**
		 * 战败装载处理
		 */
		defeat:function(){return this._install_("defeat",arguments,false);},
		/**
		 * 无论是否胜利或者战败，都将执行这些命令
		 */
		mush:function(){return this._install_("mush",arguments,true);},
		/**
		 * 执行
		 */
		_execute_:function(type,command){
			var cmds = this.cmds,cmd,next;
			if(!cmds) return this;
			for(var k in cmds){
				cmd = cmds[k];
				if(cmd.always || cmd.type === type) {
					next = cmd.cmd.apply(this,command);
					if(this.assert &&  !next) break;
				} 
			}
			this.perish();
			return this;
		},
		/**
		 * 攻击命令
		 */
		attack:function(){return this._execute_("victory",arguments);},
		/**
		 * 撤退命令
		 */
		retreat:function(){return this._execute_("defeat",arguments);},
		/**
		 * 灭亡
		 */
		perish:function(){this.cmds.splice(0,this.cmds.length);},
		/**
		 * 入队
		 */
		enter:function(){this._install_("queue",arguments,false);this.length = this.queue.length;return this;},
		/**
		 * 出队
		 */
		out:function() {var item= this.queue.shift();this.length = this.queue.length;return item;},
		/**
		 * 获取队首数据
		 */
		peek:function(){return this.queue[0];	},
		/**
		 * 清空对
		 */
		clear:function(){this.queue.splice(0,this.queue.length);this.length = this.queue.length;this.isGo = false;},
		/**
		 * 执行队列
		 */
		go:function(force){
			if(this.isGo && !force) return this;
			this.isGo = true;
			var self =this,timer;
			timer = window.setTimeout(function(){
				var front = self.out(),next,clear,ret;
				self.current = front;
				if(front === undefined) {self.isGo = false;return self;}
				next = function(){self.go(true);};
				clear = function(){self.clear();};
				//执行当前方法
				ret = front.call(self.commander,next,clear);
				if(ret) self.currentRun.push(ret);
				window.clearTimeout(timer);
				timer = undefined;
			},0);
			return this;
		},
		getCurrent:function(){
			return this.current;
		},
		getCurrentRun:function(){
			return this.currentRun;
		},
		currentIterator:function(callback) {
			var node;
			while((node = this.currentRun.shift())){
				callback(node);
			}
		}
	});
	jBud.Links = function(commander){return new Links(commander);};
	/*# Links end #*/
	
	/*# Ready start #*/
	var readyLinks;
	var isReady = false;
	var readyComplete = function(event){
		if ( document.addEventListener || event.type === "load" || document.readyState === "complete" ) {
			readyLinks.attack(isReady);
			isReady = true;
		}
	};
	var readyScroll = function(){
		var top = false;
		try {
			top = window.frameElement == null && document.documentElement;
		} catch(e) {}
		if ( top && top.doScroll ) {
			if (isReady ) {
				try {
					top.doScroll("left");
				} catch(e) {
					return setTimeout( readyScroll, 50 );
				}
				if ( document.addEventListener ) {
					document.removeEventListener( "DOMContentLoaded",readyComplete , false );
					window.removeEventListener( "load", readyComplete, false );
				} else {
					document.detachEvent( "onreadystatechange", readyComplete );
					window.detachEvent( "onload", readyComplete );
				}
				jBud.ready();
			}
		}
	};
	/**
	 * 等待页面加载完成后触发响应事件
	 */
	jBud.ready = function(callback){
		if(!readyLinks) {
			readyLinks = jBud.Links();
			if ( document.readyState === "complete" ) {
				setTimeout( jBud.ready,50);
			} else if ( document.addEventListener ) {
				document.addEventListener( "DOMContentLoaded", readyComplete, false );
				window.addEventListener( "load", readyComplete, false );
			} else {
				document.attachEvent( "onreadystatechange", readyComplete );
				window.attachEvent( "onload", readyComplete );
				readyScroll();
			}
		}
		if(jBud.isFunction(callback)) {
			readyLinks.victory(callback);
		}
		if(isReady) readyLinks.attack(isReady);
		return readyLinks;
	};
	/*# Ready end #*/
})(window);