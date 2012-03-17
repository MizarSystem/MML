<?xml version='1.0' encoding='UTF-8'?>

<!-- This file is now automatically produced from the files in the MHTML directory. -->
<!-- Its only reason is to have just one big .xsl file in the Mizar distro. -->
<!-- So any changes should be done to the MHTML files, running 'make miz.xsl' afterwards. -->
<!-- The main stylesheet mhtml_main.xsl can be used instead miz.xsl, -->
<!-- provided the included .xsl files are available in the same directory -->
<xsl:stylesheet version="1.0" extension-element-prefixes="dc" xmlns:dc="http://purl.org/dc/elements/1.1/" xmlns:xsl="http://www.w3.org/1999/XSL/Transform">
  <xsl:output method="html"/>
  <!-- $Revision: 1.63 $ -->
  <!--  -->
  <!-- File: mhtml_main.xsltxt - html-ization of Mizar XML, main file -->
  <!--  -->
  <!-- Author: Josef Urban -->
  <!--  -->
  <!-- License: GPL (GNU GENERAL PUBLIC LICENSE) -->
  <!-- XSLTXT (https://xsltxt.dev.java.net/) stylesheet taking -->
  <!-- XML terms, formulas and types to less verbose format. -->
  <!-- To produce standard XSLT from this do e.g.: -->
  <!-- java -jar xsltxt.jar toXSL miz.xsltxt | sed -e 's/<!\-\- *\(<\/*xsl:document.*\) *\-\->/\1/g' >miz.xsl -->
  <!-- (the sed hack is there because xsl:document is not yet supported by xsltxtx) -->
  <!-- Then e.g.: xsltproc miz.xsl ordinal2.pre >ordinal2.pre1 -->
  <!-- TODO: number B vars in fraenkel - done since 1.72 -->
  <!-- handle F and H parenthesis as K parenthesis -->
  <!-- article numbering in Ref? -->
  <!-- absolute definiens numbers for thesisExpansions? - done -->
  <!-- do not display BlockThesis for Proof? - done, should but should be optional for Now -->
  <!-- add @nr to canceled -->
  <!-- Constructor should know its serial number! - needed in defs -->
  <!-- possibly also article? -->
  <!-- change globally 'G' to 'L' for types? -> then change the -->
  <!-- hacks here and in emacs.el -->
  <!-- display definiens? - done -->
  <!-- NOTES: constructor disambiguation is done using the absolute numbers -->
  <!-- (attribute 'nr' and 'aid' of the Constructor element. -->
  <!-- This info for Constructors not defined in the article is -->
  <!-- taken from the .atr file (see variable $constrs) -->
  <!--  -->
  <!-- File: params.xsltxt - html-ization of Mizar XML, top-level parameters -->
  <!--  -->
  <!-- Author: Josef Urban -->
  <!--  -->
  <!-- License: GPL (GNU GENERAL PUBLIC LICENSE) -->
  <!-- The following are user-customizable -->
  <!-- mmlquery address -->
  <xsl:param name="mmlq">
    <xsl:text>http://merak.pb.bialystok.pl/mmlquery/fillin.php?entry=</xsl:text>
  </xsl:param>
  <!-- #mmlq= {"";} -->
  <!-- linking methods: -->
  <!-- "q" - query, everything is linked to mmlquery -->
  <!-- "s" - self, everything is linked to these xml/html files -->
  <!-- "m" - mizaring and mmlquery, current article's constructs are linked to self, -->
  <!-- the rest is linked to mmlquery -->
  <!-- "l" - local mizaring, current article's constructs are linked to self, -->
  <!-- the rest to $MIZFILES/html -->
  <xsl:param name="linking">
    <xsl:text>l</xsl:text>
  </xsl:param>
  <!-- needed for local linking, document("") gives the sylesheet as a document -->
  <xsl:param name="mizfiles">
    <xsl:value-of select="string(/*/@mizfiles)"/>
  </xsl:param>
  <xsl:param name="mizhtml">
    <xsl:value-of select="concat(&quot;file://&quot;,$mizfiles,&quot;html/&quot;)"/>
  </xsl:param>
  <!-- extension for linking to other articles - either xml or html -->
  <xsl:param name="ext">
    <xsl:text>html</xsl:text>
  </xsl:param>
  <!-- extension for linking to other articles - either xml or html -->
  <xsl:param name="selfext">
    <xsl:choose>
      <xsl:when test="$linking = &quot;l&quot;">
        <xsl:text>xml</xsl:text>
      </xsl:when>
      <xsl:when test="$linking = &quot;s&quot;">
        <xsl:value-of select="$ext"/>
      </xsl:when>
      <xsl:when test="$linking = &quot;m&quot;">
        <xsl:text>xml</xsl:text>
      </xsl:when>
      <xsl:when test="$linking = &quot;q&quot;">
        <xsl:text>html</xsl:text>
      </xsl:when>
    </xsl:choose>
  </xsl:param>
  <!-- default target frame for links -->
  <xsl:param name="default_target">
    <xsl:choose>
      <xsl:when test="$linking = &quot;s&quot;">
        <xsl:text>_self</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>mmlquery</xsl:text>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:param>
  <!-- put titles to links or not -->
  <xsl:param name="titles">
    <xsl:text>0</xsl:text>
  </xsl:param>
  <!-- coloured output or not -->
  <xsl:param name="colored">
    <xsl:text>0</xsl:text>
  </xsl:param>
  <!-- print identifiers (like in JFM) instead of normalized names -->
  <xsl:variable name="print_identifiers">
    <xsl:text>1</xsl:text>
  </xsl:variable>
  <!-- print label identifiers  instead of normalized names -->
  <!-- this is kept separate from $print_identifiers, because -->
  <!-- it should be turned off for item generating -->
  <xsl:variable name="print_lab_identifiers">
    <xsl:text>1</xsl:text>
  </xsl:variable>
  <!-- tells whether relative or absolute names are shown -->
  <xsl:param name="relnames">
    <xsl:text>1</xsl:text>
  </xsl:param>
  <!-- link by (now also from) inferences to ATP solutions rendered by MMLQuery; experimental - off -->
  <!-- 1 - static linking (to pre-generated html) -->
  <!-- 2 - dynamic linking to MML Query (static dli sent to MMLQuery DLI-processor) -->
  <!-- 3 - dynamic linking to the TPTP-processor CGI ($lbytptpcgi) -->
  <xsl:param name="linkby">
    <xsl:text>0</xsl:text>
  </xsl:param>
  <!-- if > 0, call the mk_by_title function to create a title for by|from|; -->
  <xsl:param name="by_titles">
    <xsl:text>0</xsl:text>
  </xsl:param>
  <!-- If 1, the target frame for by explanations is _self -->
  <xsl:param name="linkbytoself">
    <xsl:text>0</xsl:text>
  </xsl:param>
  <!-- directory with by ATP solutions in HTML; each article in its own subdir -->
  <xsl:param name="lbydir">
    <xsl:text>_by/</xsl:text>
  </xsl:param>
  <!-- directory with by ATP solutions in DLI; each article in its own subdir -->
  <!-- now whole url for the CGI script -->
  <xsl:param name="lbydliurl">
    <xsl:text>http://lipa.ms.mff.cuni.cz/~urban/xmlmml/html.930/_by_dli/</xsl:text>
  </xsl:param>
  <!-- URL of the DLI-processor CGI -->
  <xsl:param name="lbydlicgi">
    <xsl:text>http://mmlquery.mizar.org/cgi-bin/mmlquery/dli</xsl:text>
  </xsl:param>
  <!-- complete prefix of the DLI-processor CGI request -->
  <xsl:variable name="lbydlicgipref">
    <xsl:value-of select="concat($lbydlicgi,&quot;?url=&quot;,$lbydliurl)"/>
  </xsl:variable>
  <!-- URL of the TPTP-processor CGI -->
  <xsl:param name="lbytptpcgi">
    <xsl:text>http://octopi.mizar.org/~mptp/cgi-bin/showby.cgi</xsl:text>
  </xsl:param>
  <!-- tells if by action is fetched through AJAX; default is off -->
  <xsl:param name="ajax_by">
    <xsl:text>0</xsl:text>
  </xsl:param>
  <!-- temporary dir with  the tptp by files, needs to be passed as a param -->
  <xsl:param name="lbytmpdir">
    <xsl:text/>
  </xsl:param>
  <!-- tells if linkage of proof elements is done; default is off -->
  <xsl:param name="proof_links">
    <xsl:text>0</xsl:text>
  </xsl:param>
  <!-- tells if linkage of constants is done; default is 0 (off), -->
  <!-- 1 tells to only create the anchors, 2 tells to also link constants -->
  <!-- ##TODO: 2 is implement incorrectly and should not be used now, -->
  <!-- it should be done like privname (via the C key, not like now) -->
  <xsl:param name="const_links">
    <xsl:text>0</xsl:text>
  </xsl:param>
  <!-- tells if proofs are fetched through AJAX; default is off -->
  <xsl:param name="ajax_proofs">
    <xsl:text>0</xsl:text>
  </xsl:param>
  <!-- the dir with proofs that are fetched through AJAX -->
  <xsl:param name="ajax_proof_dir">
    <xsl:text>proofs</xsl:text>
  </xsl:param>
  <!-- tells to display thesis after skeleton items -->
  <xsl:param name="display_thesis">
    <xsl:text>1</xsl:text>
  </xsl:param>
  <!-- tells if only selected items are generated to subdirs; default is off -->
  <xsl:param name="generate_items">
    <xsl:text>0</xsl:text>
  </xsl:param>
  <!-- relevant only if $generate_items>0 -->
  <!-- tells if proofs of selected items are generated to subdirs; default is off -->
  <xsl:param name="generate_items_proofs">
    <xsl:text>0</xsl:text>
  </xsl:param>
  <!-- add IDV links and icons -->
  <xsl:param name="idv">
    <xsl:text>0</xsl:text>
  </xsl:param>
  <!-- create header info from .hdr file -->
  <xsl:param name="mk_header">
    <xsl:text>0</xsl:text>
  </xsl:param>
  <xsl:variable name="lcletters">
    <xsl:text>abcdefghijklmnopqrstuvwxyz</xsl:text>
  </xsl:variable>
  <xsl:variable name="ucletters">
    <xsl:text>ABCDEFGHIJKLMNOPQRSTUVWXYZ</xsl:text>
  </xsl:variable>
  <!-- name of current article (upper case) -->
  <xsl:param name="aname">
    <xsl:value-of select="string(/*/@aid)"/>
  </xsl:param>
  <!-- name of current article (lower case) -->
  <xsl:param name="anamelc">
    <xsl:value-of select="translate($aname, $ucletters, $lcletters)"/>
  </xsl:param>
  <!-- this needs to be set to 1 for processing MML files -->
  <xsl:param name="mml">
    <xsl:choose>
      <xsl:when test="/Article">
        <xsl:text>0</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>1</xsl:text>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:param>
  <!-- nr. of clusters in Typ -->
  <!-- this is set to 1 for processing MML files -->
  <xsl:param name="cluster_nr">
    <xsl:choose>
      <xsl:when test="$mml = &quot;0&quot;">
        <xsl:text>2</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>1</xsl:text>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:param>
  <!-- whether we print all attributes (not just those with @pid) -->
  <!-- this is set to 1 for processing MML files -->
  <xsl:param name="print_all_attrs">
    <xsl:value-of select="$mml"/>
  </xsl:param>
  <!-- .atr file with imported constructors -->
  <xsl:param name="constrs">
    <xsl:value-of select="concat($anamelc, &apos;.atr&apos;)"/>
  </xsl:param>
  <!-- .eth file with imported theorems -->
  <xsl:param name="thms">
    <xsl:value-of select="concat($anamelc, &apos;.eth&apos;)"/>
  </xsl:param>
  <!-- .esh file with imported schemes -->
  <xsl:param name="schms">
    <xsl:value-of select="concat($anamelc, &apos;.esh&apos;)"/>
  </xsl:param>
  <!-- .eno file with imported patterns -->
  <xsl:param name="patts">
    <xsl:value-of select="concat($anamelc, &apos;.eno&apos;)"/>
  </xsl:param>
  <!-- .frx file with all (both imported and article's) formats -->
  <xsl:param name="formats">
    <xsl:value-of select="concat($anamelc, &apos;.frx&apos;)"/>
  </xsl:param>
  <!-- .dcx file with vocabulary -->
  <xsl:param name="vocs">
    <xsl:value-of select="concat($anamelc, &apos;.dcx&apos;)"/>
  </xsl:param>
  <!-- .idx file with identifier names -->
  <xsl:param name="ids">
    <xsl:value-of select="concat($anamelc, &apos;.idx&apos;)"/>
  </xsl:param>
  <!-- .dfs file with imported definientia -->
  <xsl:param name="dfs">
    <xsl:value-of select="concat($anamelc, &apos;.dfs&apos;)"/>
  </xsl:param>
  <!-- .hdr file with header info (done by mkxmlhdr.pl) -->
  <xsl:param name="hdr">
    <xsl:value-of select="concat($anamelc, &apos;.hdr&apos;)"/>
  </xsl:param>
  <xsl:param name="varcolor">
    <xsl:text>Olive</xsl:text>
  </xsl:param>
  <xsl:param name="constcolor">
    <xsl:text>Maroon</xsl:text>
  </xsl:param>
  <xsl:param name="locicolor">
    <xsl:text>Maroon</xsl:text>
  </xsl:param>
  <xsl:param name="schpcolor">
    <xsl:text>Maroon</xsl:text>
  </xsl:param>
  <xsl:param name="schfcolor">
    <xsl:text>Maroon</xsl:text>
  </xsl:param>
  <xsl:param name="ppcolor">
    <xsl:text>Maroon</xsl:text>
  </xsl:param>
  <xsl:param name="pfcolor">
    <xsl:text>Maroon</xsl:text>
  </xsl:param>
  <xsl:param name="labcolor">
    <xsl:text>Green</xsl:text>
  </xsl:param>
  <xsl:param name="commentcolor">
    <xsl:text>Red</xsl:text>
  </xsl:param>
  <!-- use spans for brackets -->
  <xsl:param name="parenspans">
    <xsl:text>1</xsl:text>
  </xsl:param>
  <!-- number of parenthesis colors (see the stylesheet in the bottom) -->
  <xsl:param name="pcolors_nr">
    <xsl:text>6</xsl:text>
  </xsl:param>
  <!-- top level element instead of top-level document, which is hard to -->
  <!-- know -->
  <xsl:param name="top" select="/"/>
  <!-- debugging message -->
  <xsl:param name="dbgmsg">
    <xsl:text>zzzzzzzzz</xsl:text>
  </xsl:param>
  <!-- relative nr of the first expandable mode -->
  <!-- #first_exp = { `//Pattern[(@constrkind='M') and (@constrnr=0)][1]/@relnr`; } -->
  <!--  -->
  <!-- File: keys.xsltxt - html-ization of Mizar XML, definition of keys (indexes) -->
  <!--  -->
  <!-- Author: Josef Urban -->
  <!--  -->
  <!-- License: GPL (GNU GENERAL PUBLIC LICENSE) -->
  <!-- keys for fast constructor and reference lookup -->
  <xsl:key name="M" match="Constructor[@kind=&apos;M&apos;]" use="@relnr"/>
  <xsl:key name="L" match="Constructor[@kind=&apos;L&apos;]" use="@relnr"/>
  <xsl:key name="V" match="Constructor[@kind=&apos;V&apos;]" use="@relnr"/>
  <xsl:key name="R" match="Constructor[@kind=&apos;R&apos;]" use="@relnr"/>
  <xsl:key name="K" match="Constructor[@kind=&apos;K&apos;]" use="@relnr"/>
  <xsl:key name="U" match="Constructor[@kind=&apos;U&apos;]" use="@relnr"/>
  <xsl:key name="G" match="Constructor[@kind=&apos;G&apos;]" use="@relnr"/>
  <xsl:key name="T" match="/Theorems/Theorem[@kind=&apos;T&apos;]" use="concat(@articlenr,&apos;:&apos;,@nr)"/>
  <xsl:key name="D" match="/Theorems/Theorem[@kind=&apos;D&apos;]" use="concat(@articlenr,&apos;:&apos;,@nr)"/>
  <xsl:key name="S" match="/Schemes/Scheme" use="concat(@articlenr,&apos;:&apos;,@nr)"/>
  <xsl:key name="DF" match="Definiens" use="@relnr"/>
  <!-- patterns are slightly tricky, since a predicate pattern -->
  <!-- may be linked to an attribute constructor; hence the -->
  <!-- indexing is done according to @constrkind and not @kind -->
  <!-- TODO: the attribute<->predicate change should propagate to usage -->
  <!-- of "is" -->
  <!-- Expandable modes have all @constrkind='M' and @constrnr=0, -->
  <!-- they are indexed separately only on their @relnr (@pid) -->
  <xsl:key name="P_M" match="Pattern[(@constrkind=&apos;M&apos;) and (@constrnr&gt;0)]" use="@constrnr"/>
  <xsl:key name="P_L" match="Pattern[@constrkind=&apos;L&apos;]" use="@constrnr"/>
  <xsl:key name="P_V" match="Pattern[@constrkind=&apos;V&apos;]" use="@constrnr"/>
  <xsl:key name="P_R" match="Pattern[@constrkind=&apos;R&apos;]" use="@constrnr"/>
  <xsl:key name="P_K" match="Pattern[@constrkind=&apos;K&apos;]" use="@constrnr"/>
  <xsl:key name="P_U" match="Pattern[@constrkind=&apos;U&apos;]" use="@constrnr"/>
  <xsl:key name="P_G" match="Pattern[@constrkind=&apos;G&apos;]" use="@constrnr"/>
  <xsl:key name="EXP" match="Pattern[(@constrkind=&apos;M&apos;) and (@constrnr=0)]" use="@relnr"/>
  <xsl:key name="F" match="Format" use="@nr"/>
  <xsl:key name="D_G" match="Symbol[@kind=&apos;G&apos;]" use="@nr"/>
  <xsl:key name="D_K" match="Symbol[@kind=&apos;K&apos;]" use="@nr"/>
  <xsl:key name="D_J" match="Symbol[@kind=&apos;J&apos;]" use="@nr"/>
  <xsl:key name="D_L" match="Symbol[@kind=&apos;L&apos;]" use="@nr"/>
  <xsl:key name="D_M" match="Symbol[@kind=&apos;M&apos;]" use="@nr"/>
  <xsl:key name="D_O" match="Symbol[@kind=&apos;O&apos;]" use="@nr"/>
  <xsl:key name="D_R" match="Symbol[@kind=&apos;R&apos;]" use="@nr"/>
  <xsl:key name="D_U" match="Symbol[@kind=&apos;U&apos;]" use="@nr"/>
  <xsl:key name="D_V" match="Symbol[@kind=&apos;V&apos;]" use="@nr"/>
  <!-- identifiers -->
  <xsl:key name="D_I" match="Symbol[@kind=&apos;I&apos;]" use="@nr"/>
  <!-- keys for absolute linkage inside proofs; -->
  <!-- requires preprocessing by addabsrefs, otherwise wrong results, -->
  <!-- so commented now (could be uncommented using conditional include probably) -->
  <!-- lookup for local constants -->
  <xsl:key name="C" match="Let|Given|TakeAsVar|Consider|Set|Reconsider" use="@plevel"/>
  <!-- lookup for propositions -->
  <xsl:key name="E" match="Proposition|IterEquality|Now" use="concat(@nr,&quot;:&quot;,@plevel)"/>
  <!-- lookup for scheme functors and predicates -->
  <xsl:key name="f" match="SchemeFuncDecl" use="concat(@nr,&quot;:&quot;,@plevel)"/>
  <xsl:key name="p" match="SchemePredDecl" use="concat(@nr,&quot;:&quot;,@plevel)"/>
  <!-- lookup for private functors and predicates -->
  <xsl:key name="pf" match="DefFunc" use="concat(@nr,&quot;:&quot;,@plevel)"/>
  <xsl:key name="pp" match="DefPred" use="concat(@nr,&quot;:&quot;,@plevel)"/>

  <!--  -->
  <!-- File: print_simple.xsltxt - html-ization of Mizar XML, simple printing funcs -->
  <!--  -->
  <!-- Author: Josef Urban -->
  <!--  -->
  <!-- License: GPL (GNU GENERAL PUBLIC LICENSE) -->
  <!-- pretty print variables and labels -->
  <!-- ##TODO: link variables and consts to their introduction? -->
  <!-- private - look up the name of id -->
  <xsl:template name="get_vid_name">
    <xsl:param name="vid"/>
    <xsl:for-each select="document($ids, /)">
      <xsl:for-each select="key(&apos;D_I&apos;, $vid)">
        <xsl:value-of select="@name"/>
      </xsl:for-each>
    </xsl:for-each>
  </xsl:template>

  <xsl:template name="pqvar">
    <xsl:param name="nr"/>
    <xsl:param name="vid"/>
    <xsl:choose>
      <xsl:when test="($print_identifiers &gt; 0) and ($vid &gt; 0)">
        <xsl:variable name="nm">
          <xsl:call-template name="get_vid_name">
            <xsl:with-param name="vid" select="$vid"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:choose>
          <xsl:when test="$colored = &quot;1&quot;">
            <xsl:element name="font">
              <xsl:attribute name="color">
                <xsl:value-of select="$varcolor"/>
              </xsl:attribute>
              <xsl:if test="$titles=&quot;1&quot;">
                <xsl:attribute name="title">
                  <xsl:value-of select="concat(&quot;b&quot;,$nr)"/>
                </xsl:attribute>
              </xsl:if>
              <xsl:value-of select="$nm"/>
            </xsl:element>
          </xsl:when>
          <xsl:otherwise>
            <xsl:value-of select="$nm"/>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="pvar">
          <xsl:with-param name="nr" select="$nr"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="pvar">
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="$colored=&quot;1&quot;">
        <xsl:element name="font">
          <xsl:attribute name="color">
            <xsl:value-of select="$varcolor"/>
          </xsl:attribute>
          <xsl:text>b</xsl:text>
          <xsl:element name="sub">
            <xsl:value-of select="$nr"/>
          </xsl:element>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>b</xsl:text>
        <xsl:element name="sub">
          <xsl:value-of select="$nr"/>
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="pconst">
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="$colored=&quot;1&quot;">
        <xsl:element name="font">
          <xsl:attribute name="color">
            <xsl:value-of select="$constcolor"/>
          </xsl:attribute>
          <xsl:text>c</xsl:text>
          <xsl:element name="sub">
            <xsl:value-of select="$nr"/>
          </xsl:element>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>c</xsl:text>
        <xsl:element name="sub">
          <xsl:value-of select="$nr"/>
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- #pl gives the optional proof level -->
  <xsl:template name="ppconst">
    <xsl:param name="nr"/>
    <xsl:param name="vid"/>
    <xsl:param name="pl"/>
    <xsl:choose>
      <xsl:when test="($print_identifiers &gt; 0) and ($vid &gt; 0)">
        <xsl:variable name="ctarget">
          <xsl:choose>
            <xsl:when test="($const_links&gt;0) and  ($pl)">
              <xsl:text>c</xsl:text>
              <xsl:value-of select="$nr"/>
              <xsl:call-template name="addp">
                <xsl:with-param name="pl" select="$pl"/>
              </xsl:call-template>
            </xsl:when>
            <xsl:otherwise>
              <xsl:value-of select="concat(&quot;c&quot;,$nr)"/>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:variable name="nm">
          <xsl:call-template name="get_vid_name">
            <xsl:with-param name="vid" select="$vid"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:choose>
          <xsl:when test="($const_links=2)">
            <xsl:element name="a">
              <xsl:attribute name="class">
                <xsl:text>txt</xsl:text>
              </xsl:attribute>
              <xsl:attribute name="href">
                <xsl:value-of select="concat(&quot;#&quot;,$ctarget)"/>
              </xsl:attribute>
              <xsl:element name="font">
                <xsl:attribute name="color">
                  <xsl:value-of select="$constcolor"/>
                </xsl:attribute>
                <xsl:if test="$titles=&quot;1&quot;">
                  <xsl:attribute name="title">
                    <xsl:value-of select="$ctarget"/>
                  </xsl:attribute>
                </xsl:if>
                <xsl:value-of select="$nm"/>
              </xsl:element>
            </xsl:element>
          </xsl:when>
          <xsl:otherwise>
            <xsl:choose>
              <xsl:when test="$colored = &quot;1&quot;">
                <xsl:element name="font">
                  <xsl:attribute name="color">
                    <xsl:value-of select="$constcolor"/>
                  </xsl:attribute>
                  <xsl:if test="$titles=&quot;1&quot;">
                    <xsl:attribute name="title">
                      <xsl:value-of select="$ctarget"/>
                    </xsl:attribute>
                  </xsl:if>
                  <xsl:value-of select="$nm"/>
                </xsl:element>
              </xsl:when>
              <xsl:otherwise>
                <xsl:value-of select="$nm"/>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="pconst">
          <xsl:with-param name="nr" select="$nr"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="pploci">
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="($print_identifiers &gt; 0) and ($proof_links&gt;0)">
        <xsl:variable name="pl">
          <xsl:call-template name="get_nearest_level">
            <xsl:with-param name="el" select=".."/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:call-template name="absconst">
          <xsl:with-param name="nr" select="@nr"/>
          <xsl:with-param name="pl" select="$pl"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="pconst">
          <xsl:with-param name="nr" select="@nr"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="ploci">
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="$colored=&quot;1&quot;">
        <xsl:element name="font">
          <xsl:attribute name="color">
            <xsl:value-of select="$locicolor"/>
          </xsl:attribute>
          <xsl:text>a</xsl:text>
          <xsl:element name="sub">
            <xsl:value-of select="$nr"/>
          </xsl:element>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>a</xsl:text>
        <xsl:element name="sub">
          <xsl:value-of select="$nr"/>
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="pschpvar">
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="$colored=&quot;1&quot;">
        <xsl:element name="font">
          <xsl:attribute name="color">
            <xsl:value-of select="$schpcolor"/>
          </xsl:attribute>
          <xsl:text>P</xsl:text>
          <xsl:element name="sub">
            <xsl:value-of select="$nr"/>
          </xsl:element>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>P</xsl:text>
        <xsl:element name="sub">
          <xsl:value-of select="$nr"/>
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="pschfvar">
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="$colored=&quot;1&quot;">
        <xsl:element name="font">
          <xsl:attribute name="color">
            <xsl:value-of select="$schfcolor"/>
          </xsl:attribute>
          <xsl:text>F</xsl:text>
          <xsl:element name="sub">
            <xsl:value-of select="$nr"/>
          </xsl:element>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>F</xsl:text>
        <xsl:element name="sub">
          <xsl:value-of select="$nr"/>
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="pppred">
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="$colored=&quot;1&quot;">
        <xsl:element name="font">
          <xsl:attribute name="color">
            <xsl:value-of select="$ppcolor"/>
          </xsl:attribute>
          <xsl:text>S</xsl:text>
          <xsl:element name="sub">
            <xsl:value-of select="$nr"/>
          </xsl:element>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>S</xsl:text>
        <xsl:element name="sub">
          <xsl:value-of select="$nr"/>
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="ppfunc">
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="$colored=&quot;1&quot;">
        <xsl:element name="font">
          <xsl:attribute name="color">
            <xsl:value-of select="$pfcolor"/>
          </xsl:attribute>
          <xsl:text>H</xsl:text>
          <xsl:element name="sub">
            <xsl:value-of select="$nr"/>
          </xsl:element>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>H</xsl:text>
        <xsl:element name="sub">
          <xsl:value-of select="$nr"/>
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="pplab">
    <xsl:param name="nr"/>
    <xsl:param name="vid"/>
    <xsl:param name="txt"/>
    <xsl:choose>
      <xsl:when test="($print_lab_identifiers &gt; 0) and ($vid &gt; 0)">
        <xsl:variable name="nm">
          <xsl:call-template name="get_vid_name">
            <xsl:with-param name="vid" select="$vid"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:element name="i">
          <xsl:choose>
            <xsl:when test="$colored = &quot;1&quot;">
              <xsl:element name="font">
                <xsl:attribute name="color">
                  <xsl:value-of select="$labcolor"/>
                </xsl:attribute>
                <xsl:if test="$titles=&quot;1&quot;">
                  <xsl:attribute name="title">
                    <xsl:value-of select="concat(&quot;E&quot;,$nr)"/>
                  </xsl:attribute>
                </xsl:if>
                <xsl:value-of select="$nm"/>
              </xsl:element>
            </xsl:when>
            <xsl:otherwise>
              <xsl:value-of select="$nm"/>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:choose>
          <xsl:when test="$txt">
            <xsl:call-template name="plab1">
              <xsl:with-param name="nr" select="$nr"/>
              <xsl:with-param name="txt" select="$txt"/>
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <xsl:call-template name="plab">
              <xsl:with-param name="nr" select="$nr"/>
            </xsl:call-template>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="plab">
    <xsl:param name="nr"/>
    <xsl:element name="i">
      <xsl:choose>
        <xsl:when test="$colored=&quot;1&quot;">
          <xsl:element name="font">
            <xsl:attribute name="color">
              <xsl:value-of select="$labcolor"/>
            </xsl:attribute>
            <xsl:text>E</xsl:text>
            <xsl:value-of select="$nr"/>
          </xsl:element>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>E</xsl:text>
          <xsl:value-of select="$nr"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:element>
  </xsl:template>

  <xsl:template name="plab1">
    <xsl:param name="nr"/>
    <xsl:param name="txt"/>
    <xsl:element name="i">
      <xsl:choose>
        <xsl:when test="$colored=&quot;1&quot;">
          <xsl:element name="font">
            <xsl:attribute name="color">
              <xsl:value-of select="$labcolor"/>
            </xsl:attribute>
            <xsl:value-of select="$txt"/>
            <xsl:value-of select="$nr"/>
          </xsl:element>
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="$txt"/>
          <xsl:value-of select="$nr"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:element>
  </xsl:template>

  <xsl:template name="pcomment0">
    <xsl:param name="str"/>
    <xsl:element name="i">
      <xsl:choose>
        <xsl:when test="$colored=&quot;1&quot;">
          <xsl:element name="font">
            <xsl:attribute name="color">
              <xsl:value-of select="$commentcolor"/>
            </xsl:attribute>
            <xsl:text>:: </xsl:text>
            <xsl:value-of select="$str"/>
          </xsl:element>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>:: </xsl:text>
          <xsl:value-of select="$str"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:element>
  </xsl:template>

  <xsl:template name="pcomment">
    <xsl:param name="str"/>
    <xsl:call-template name="pcomment0">
      <xsl:with-param name="str" select="$str"/>
    </xsl:call-template>
    <xsl:element name="br"/>
  </xsl:template>

  <!-- argument list -->
  <xsl:template name="arglist">
    <xsl:param name="separ"/>
    <xsl:param name="elems"/>
    <xsl:for-each select="$elems">
      <xsl:call-template name="ploci">
        <xsl:with-param name="nr" select="position()"/>
      </xsl:call-template>
      <xsl:if test="not(position() = last())">
        <xsl:value-of select="$separ"/>
      </xsl:if>
    </xsl:for-each>
  </xsl:template>

  <!-- like jlist, but with loci -->
  <xsl:template name="alist">
    <xsl:param name="j"/>
    <xsl:param name="sep1"/>
    <xsl:param name="sep2"/>
    <xsl:param name="elems"/>
    <xsl:for-each select="$elems">
      <xsl:apply-templates select="."/>
      <xsl:if test="not(position() = last())">
        <xsl:value-of select="$sep1"/>
        <xsl:call-template name="ploci">
          <xsl:with-param name="nr" select="$j+position()"/>
        </xsl:call-template>
        <xsl:value-of select="$sep2"/>
      </xsl:if>
    </xsl:for-each>
  </xsl:template>
  <!--  -->
  <!-- File: utils.xsltxt - html-ization of Mizar XML, various utility functions -->
  <!--  -->
  <!-- Author: Josef Urban -->
  <!--  -->
  <!-- License: GPL (GNU GENERAL PUBLIC LICENSE) -->
  <xsl:param name="pid_Ex">
    <xsl:text>-1</xsl:text>
  </xsl:param>
  <!-- usually NegFrmPtr -->
  <xsl:param name="pid_Ex_Univ">
    <xsl:text>-2</xsl:text>
  </xsl:param>
  <!-- usually UnivFrmPtr -->
  <xsl:param name="pid_Ex_InnerNot">
    <xsl:text>-3</xsl:text>
  </xsl:param>
  <!-- usually NegFrmPtr -->
  <xsl:param name="pid_Impl">
    <xsl:text>-4</xsl:text>
  </xsl:param>
  <!-- usually NegFrmPtr -->
  <xsl:param name="pid_Impl_And">
    <xsl:text>-5</xsl:text>
  </xsl:param>
  <!-- usually ConjFrmPtr -->
  <xsl:param name="pid_Impl_RightNot">
    <xsl:text>-6</xsl:text>
  </xsl:param>
  <!-- usually NegFrmPtr -->
  <xsl:param name="pid_Iff">
    <xsl:text>-7</xsl:text>
  </xsl:param>
  <!-- usually ConjFrmPtr -->
  <xsl:param name="pid_Or">
    <xsl:text>-8</xsl:text>
  </xsl:param>
  <!-- usually NegFrmPtr -->
  <xsl:param name="pid_Or_And">
    <xsl:text>-9</xsl:text>
  </xsl:param>
  <!-- usually ConjFrmPtr -->
  <xsl:param name="pid_Or_LeftNot">
    <xsl:text>-10</xsl:text>
  </xsl:param>
  <!-- usually NegFrmPtr -->
  <xsl:param name="pid_Or_RightNot">
    <xsl:text>-11</xsl:text>
  </xsl:param>

  <!-- usually NegFrmPtr -->
  <!-- means that "not" will not be used -->
  <xsl:template name="is_positive">
    <xsl:param name="el"/>
    <xsl:for-each select="$el">
      <xsl:choose>
        <xsl:when test="(name()=&quot;Not&quot;)">
          <xsl:choose>
            <xsl:when test="Pred[(@kind=&apos;V&apos;) or (@kind=&apos;R&apos;)]">
              <xsl:variable name="pi">
                <xsl:call-template name="patt_info">
                  <xsl:with-param name="k" select="*[1]/@kind"/>
                  <xsl:with-param name="nr" select="*[1]/@nr"/>
                  <xsl:with-param name="pid" select="*[1]/@pid"/>
                </xsl:call-template>
              </xsl:variable>
              <xsl:variable name="antonym">
                <xsl:call-template name="cadr">
                  <xsl:with-param name="l" select="$pi"/>
                </xsl:call-template>
              </xsl:variable>
              <xsl:value-of select="$antonym mod 2"/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:text>0</xsl:text>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:when>
        <xsl:otherwise>
          <xsl:choose>
            <xsl:when test="(name()=&quot;Pred&quot;) and ((@kind=&apos;V&apos;) or (@kind=&apos;R&apos;))">
              <xsl:variable name="pi">
                <xsl:call-template name="patt_info">
                  <xsl:with-param name="k" select="@kind"/>
                  <xsl:with-param name="nr" select="@nr"/>
                  <xsl:with-param name="pid" select="@pid"/>
                </xsl:call-template>
              </xsl:variable>
              <xsl:variable name="antonym">
                <xsl:call-template name="cadr">
                  <xsl:with-param name="l" select="$pi"/>
                </xsl:call-template>
              </xsl:variable>
              <xsl:value-of select="($antonym + 1) mod 2"/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:text>1</xsl:text>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <xsl:template name="is_negative">
    <xsl:param name="el"/>
    <xsl:variable name="pos">
      <xsl:call-template name="is_positive">
        <xsl:with-param name="el" select="$el"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:value-of select="1 - $pos"/>
  </xsl:template>

  <xsl:template name="count_positive">
    <xsl:param name="els"/>
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="$nr &gt; 0">
        <xsl:variable name="el1" select="$els[position()=$nr]"/>
        <xsl:variable name="res1">
          <xsl:call-template name="is_positive">
            <xsl:with-param name="el" select="$els[position()=$nr]"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:variable name="res2">
          <xsl:call-template name="count_positive">
            <xsl:with-param name="els" select="$els"/>
            <xsl:with-param name="nr" select="$nr - 1"/>
          </xsl:call-template>
        </xsl:variable>
        <!-- DEBUG       `concat($res1,":",$res2)`; -->
        <xsl:value-of select="$res1 + $res2"/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>0</xsl:text>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- if $neg, then put negative, striping the negation -->
  <xsl:template name="put_positive">
    <xsl:param name="separ"/>
    <xsl:param name="els"/>
    <xsl:param name="nr"/>
    <xsl:param name="neg"/>
    <xsl:param name="i"/>
    <xsl:if test="$nr &gt; 0">
      <xsl:variable name="el1" select="$els[position()=1]"/>
      <xsl:variable name="pos">
        <xsl:call-template name="is_positive">
          <xsl:with-param name="el" select="$el1"/>
        </xsl:call-template>
      </xsl:variable>
      <xsl:variable name="pos1">
        <xsl:choose>
          <xsl:when test="$neg=&quot;1&quot;">
            <xsl:value-of select="($neg + $pos) mod 2"/>
          </xsl:when>
          <xsl:otherwise>
            <xsl:value-of select="$pos"/>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:variable>
      <xsl:if test="$pos1=&quot;1&quot;">
        <xsl:variable name="nm" select="name($el1)"/>
        <xsl:choose>
          <xsl:when test="$neg=&quot;1&quot;">
            <!-- change this if is_positive changes! -->
            <xsl:choose>
              <xsl:when test="$nm=&quot;Not&quot;">
                <xsl:apply-templates select="$el1/*[1]">
                  <xsl:with-param name="i" select="$i"/>
                </xsl:apply-templates>
              </xsl:when>
              <xsl:when test="$nm=&quot;Pred&quot;">
                <xsl:apply-templates select="$el1">
                  <xsl:with-param name="i" select="$i"/>
                  <xsl:with-param name="not">
                    <xsl:text>1</xsl:text>
                  </xsl:with-param>
                </xsl:apply-templates>
              </xsl:when>
              <xsl:otherwise>
                <xsl:value-of select="$dbgmsg"/>
                <xsl:value-of select="$nm"/>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:when>
          <xsl:otherwise>
            <xsl:choose>
              <xsl:when test="$nm=&quot;Not&quot;">
                <xsl:apply-templates select="$el1/*[1]">
                  <xsl:with-param name="i" select="$i"/>
                  <xsl:with-param name="not">
                    <xsl:text>1</xsl:text>
                  </xsl:with-param>
                </xsl:apply-templates>
              </xsl:when>
              <xsl:otherwise>
                <xsl:apply-templates select="$el1">
                  <xsl:with-param name="i" select="$i"/>
                </xsl:apply-templates>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:otherwise>
        </xsl:choose>
        <xsl:if test="$nr &gt; 1">
          <xsl:value-of select="$separ"/>
        </xsl:if>
      </xsl:if>
      <xsl:call-template name="put_positive">
        <xsl:with-param name="separ" select="$separ"/>
        <xsl:with-param name="els" select="$els[position() &gt; 1]"/>
        <xsl:with-param name="nr" select="$nr - $pos1"/>
        <xsl:with-param name="neg" select="$neg"/>
      </xsl:call-template>
    </xsl:if>
  </xsl:template>

  <xsl:template name="is_or">
    <xsl:param name="el"/>
    <xsl:for-each select="$el">
      <xsl:choose>
        <xsl:when test="(@pid=$pid_Or) 
        and (*[1][@pid=$pid_Or_And]) and (count(*[1]/*)=2)
	and (*[1]/*[1][@pid=$pid_Or_LeftNot])
	and (*[1]/*[2][@pid=$pid_Or_RightNot])">
          <xsl:text>1</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <!-- now also used when included "or" ate the implicant -->
  <xsl:template name="is_or1">
    <xsl:param name="el"/>
    <xsl:for-each select="$el">
      <xsl:choose>
        <xsl:when test="((@pid=$pid_Or) or (@pid=$pid_Impl)) 
        and (*[1][@pid=$pid_Or_And]) and (count(*[1]/*)&gt;=2)">
          <xsl:text>1</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <!-- used when is_or failed -->
  <xsl:template name="is_or3">
    <xsl:param name="el"/>
    <xsl:for-each select="$el">
      <xsl:choose>
        <xsl:when test="(@pid=$pid_Or) 
        and (*[1][@pid=$pid_Or_And]) and (count(*[1]/*)=2)">
          <xsl:variable name="neg1">
            <xsl:call-template name="is_negative">
              <xsl:with-param name="el" select="*[1]/*[1]"/>
            </xsl:call-template>
          </xsl:variable>
          <xsl:variable name="neg2">
            <xsl:call-template name="is_negative">
              <xsl:with-param name="el" select="*[1]/*[2]"/>
            </xsl:call-template>
          </xsl:variable>
          <xsl:value-of select="$neg1 * $neg2"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <!-- used when is_or3 failed -->
  <xsl:template name="is_or4">
    <xsl:param name="el"/>
    <xsl:for-each select="$el">
      <xsl:choose>
        <xsl:when test="(@pid=$pid_Or) 
        and (*[1][@pid=$pid_Or_And]) and (count(*[1]/*)=2)">
          <xsl:text>1</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <xsl:template name="is_impl">
    <xsl:param name="el"/>
    <xsl:for-each select="$el">
      <xsl:choose>
        <xsl:when test="(@pid=$pid_Impl) 
        and (*[1][@pid=$pid_Impl_And]) and (count(*[1]/*)=2)
	and (*[1]/*[2][@pid=$pid_Impl_RightNot])">
          <xsl:text>1</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <xsl:template name="is_impl1">
    <xsl:param name="el"/>
    <xsl:for-each select="$el">
      <xsl:choose>
        <xsl:when test="(@pid=$pid_Impl) 
        and (*[1][@pid=$pid_Impl_And]) and (count(*[1]/*)&gt;=2)">
          <xsl:choose>
            <xsl:when test="*[1]/*[@pid=$pid_Impl_RightNot]">
              <xsl:text>2</xsl:text>
            </xsl:when>
            <xsl:when test="name(*[1]/*[position()=last()]) = &quot;For&quot;">
              <xsl:text>4</xsl:text>
            </xsl:when>
            <xsl:otherwise>
              <xsl:variable name="neg1">
                <xsl:call-template name="is_negative">
                  <xsl:with-param name="el" select="*[1]/*[position()=last()]"/>
                </xsl:call-template>
              </xsl:variable>
              <xsl:choose>
                <xsl:when test="$neg1 = &quot;1&quot;">
                  <xsl:text>3</xsl:text>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:text>5</xsl:text>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <xsl:template name="is_impl2">
    <xsl:param name="el"/>
    <xsl:for-each select="$el">
      <xsl:choose>
        <xsl:when test="(@pid=$pid_Impl) 
        and (*[1][@pid=$pid_Impl_And]) and (count(*[1]/*)&gt;=2)
	and ((*[1]/*[@pid=$pid_Impl_RightNot]))">
          <xsl:text>1</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <!-- used when is_impl2 failed -->
  <xsl:template name="is_impl3">
    <xsl:param name="el"/>
    <xsl:for-each select="$el">
      <xsl:choose>
        <xsl:when test="(@pid=$pid_Impl) 
        and (*[1][@pid=$pid_Impl_And]) and (count(*[1]/*)&gt;=2)">
          <xsl:call-template name="is_negative">
            <xsl:with-param name="el" select="*[1]/*[position()=last()]"/>
          </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <!-- used when is_impl3 failed -->
  <xsl:template name="is_impl4">
    <xsl:param name="el"/>
    <xsl:for-each select="$el">
      <xsl:choose>
        <xsl:when test="(@pid=$pid_Impl) 
        and (*[1][@pid=$pid_Impl_And]) and (count(*[1]/*)&gt;=2)
	and (name(*[1]/*[position()=last()]) = &quot;For&quot;)">
          <xsl:text>1</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <!-- used when is_impl4 failed -->
  <xsl:template name="is_impl5">
    <xsl:param name="el"/>
    <xsl:for-each select="$el">
      <xsl:choose>
        <xsl:when test="(@pid=$pid_Impl) 
        and (*[1][@pid=$pid_Impl_And]) and (count(*[1]/*)&gt;=2)">
          <xsl:text>1</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <xsl:template name="is_equiv">
    <xsl:param name="el"/>
    <xsl:for-each select="$el">
      <xsl:variable name="e1">
        <xsl:choose>
          <xsl:when test="(@pid=$pid_Iff) and (count(*)=2)">
            <xsl:variable name="i1">
              <xsl:call-template name="is_impl">
                <xsl:with-param name="el" select="$el/*[1]"/>
              </xsl:call-template>
            </xsl:variable>
            <xsl:choose>
              <xsl:when test="$i1=&quot;1&quot;">
                <xsl:call-template name="is_impl">
                  <xsl:with-param name="el" select="*[2]"/>
                </xsl:call-template>
              </xsl:when>
              <xsl:otherwise>
                <xsl:text>0</xsl:text>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:when>
          <xsl:otherwise>
            <xsl:text>0</xsl:text>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:variable>
      <xsl:choose>
        <xsl:when test="$e1=&quot;1&quot;">
          <xsl:variable name="res1">
            <xsl:call-template name="are_equal">
              <xsl:with-param name="el1" select="*[1]/*[1]/*[1]"/>
              <xsl:with-param name="el2" select="*[2]/*[1]/*[2]/*[1]"/>
            </xsl:call-template>
          </xsl:variable>
          <xsl:variable name="res2">
            <xsl:call-template name="are_equal">
              <xsl:with-param name="el1" select="*[2]/*[1]/*[1]"/>
              <xsl:with-param name="el2" select="*[1]/*[1]/*[2]/*[1]"/>
            </xsl:call-template>
          </xsl:variable>
          <xsl:choose>
            <xsl:when test="($res1=&quot;1&quot;) and ($res2=&quot;1&quot;)">
              <xsl:text>1</xsl:text>
            </xsl:when>
            <xsl:otherwise>
              <xsl:text>0</xsl:text>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="$e1"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <!-- recursive equality on subnodes and attributes -->
  <xsl:template name="are_equal">
    <xsl:param name="el1"/>
    <xsl:param name="el2"/>
    <xsl:choose>
      <xsl:when test=" not(name($el1)=name($el2)) or not(count($el1/*)=count($el2/*))
	or not(count($el1/@*)=count($el2/@*))">
        <xsl:text>0</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:variable name="s1">
          <xsl:for-each select="$el1/@*">
            <xsl:value-of select="string()"/>
          </xsl:for-each>
        </xsl:variable>
        <xsl:variable name="s2">
          <xsl:for-each select="$el2/@*">
            <xsl:value-of select="string()"/>
          </xsl:for-each>
        </xsl:variable>
        <xsl:choose>
          <xsl:when test="not($s1=$s2)">
            <xsl:text>0</xsl:text>
          </xsl:when>
          <xsl:otherwise>
            <xsl:call-template name="are_equal_many">
              <xsl:with-param name="els1" select="$el1/*"/>
              <xsl:with-param name="els2" select="$el2/*"/>
              <xsl:with-param name="nr" select="count($el1/*)"/>
            </xsl:call-template>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="are_equal_many">
    <xsl:param name="els1"/>
    <xsl:param name="els2"/>
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="$nr &gt; 0">
        <xsl:variable name="el1" select="$els1[position()=$nr]"/>
        <xsl:variable name="el2" select="$els2[position()=$nr]"/>
        <xsl:variable name="res1">
          <xsl:call-template name="are_equal">
            <xsl:with-param name="el1" select="$el1"/>
            <xsl:with-param name="el2" select="$el2"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:choose>
          <xsl:when test="$res1=&quot;1&quot;">
            <xsl:call-template name="are_equal_many">
              <xsl:with-param name="els1" select="$els1"/>
              <xsl:with-param name="els2" select="$els2"/>
              <xsl:with-param name="nr" select="$nr - 1"/>
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <xsl:text>0</xsl:text>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>1</xsl:text>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- recursive equality on subnodes and attributes upto the @vid attribute -->
  <xsl:template name="are_equal_vid">
    <xsl:param name="el1"/>
    <xsl:param name="el2"/>
    <xsl:choose>
      <xsl:when test=" not(name($el1)=name($el2)) or not(count($el1/*)=count($el2/*))
	or not(count($el1/@*)=count($el2/@*))">
        <xsl:text>0</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:variable name="s1">
          <xsl:for-each select="$el1/@*">
            <xsl:if test="not(name()=&quot;vid&quot;)">
              <xsl:value-of select="string()"/>
            </xsl:if>
          </xsl:for-each>
        </xsl:variable>
        <xsl:variable name="s2">
          <xsl:for-each select="$el2/@*">
            <xsl:if test="not(name()=&quot;vid&quot;)">
              <xsl:value-of select="string()"/>
            </xsl:if>
          </xsl:for-each>
        </xsl:variable>
        <xsl:choose>
          <xsl:when test="not($s1=$s2)">
            <xsl:text>0</xsl:text>
          </xsl:when>
          <xsl:otherwise>
            <xsl:call-template name="are_equal_many_vid">
              <xsl:with-param name="els1" select="$el1/*"/>
              <xsl:with-param name="els2" select="$el2/*"/>
              <xsl:with-param name="nr" select="count($el1/*)"/>
            </xsl:call-template>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="are_equal_many_vid">
    <xsl:param name="els1"/>
    <xsl:param name="els2"/>
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="$nr &gt; 0">
        <xsl:variable name="el1" select="$els1[position()=$nr]"/>
        <xsl:variable name="el2" select="$els2[position()=$nr]"/>
        <xsl:variable name="res1">
          <xsl:call-template name="are_equal_vid">
            <xsl:with-param name="el1" select="$el1"/>
            <xsl:with-param name="el2" select="$el2"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:choose>
          <xsl:when test="$res1=&quot;1&quot;">
            <xsl:call-template name="are_equal_many_vid">
              <xsl:with-param name="els1" select="$els1"/>
              <xsl:with-param name="els2" select="$els2"/>
              <xsl:with-param name="nr" select="$nr - 1"/>
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <xsl:text>0</xsl:text>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>1</xsl:text>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="lc">
    <xsl:param name="s"/>
    <xsl:value-of select="translate($s, $ucletters, $lcletters)"/>
  </xsl:template>

  <xsl:template name="uc">
    <xsl:param name="s"/>
    <xsl:value-of select="translate($s, $lcletters, $ucletters)"/>
  </xsl:template>

  <!-- utilities for adding lemma names -->
  <xsl:template name="addp">
    <xsl:param name="pl"/>
    <xsl:if test="string-length($pl)&gt;0">
      <xsl:text>:</xsl:text>
      <xsl:value-of select="$pl"/>
    </xsl:if>
  </xsl:template>

  <xsl:template name="propname">
    <xsl:param name="n"/>
    <xsl:param name="pl"/>
    <xsl:text>E</xsl:text>
    <xsl:value-of select="$n"/>
    <xsl:call-template name="addp">
      <xsl:with-param name="pl" select="$pl"/>
    </xsl:call-template>
  </xsl:template>
  <!-- poor man's data structure, aka "colon-list" -->
  <xsl:param name="nil">
    <xsl:text/>
  </xsl:param>

  <xsl:template name="cons">
    <xsl:param name="h"/>
    <xsl:param name="t"/>
    <xsl:value-of select="concat($h,&quot;:&quot;,$t)"/>
  </xsl:template>

  <xsl:template name="car">
    <xsl:param name="l"/>
    <xsl:value-of select="substring-before($l,&quot;:&quot;)"/>
  </xsl:template>

  <xsl:template name="cdr">
    <xsl:param name="l"/>
    <xsl:value-of select="substring-after($l,&quot;:&quot;)"/>
  </xsl:template>

  <xsl:template name="cadr">
    <xsl:param name="l"/>
    <xsl:call-template name="car">
      <xsl:with-param name="l">
        <xsl:call-template name="cdr">
          <xsl:with-param name="l" select="$l"/>
        </xsl:call-template>
      </xsl:with-param>
    </xsl:call-template>
  </xsl:template>

  <xsl:template name="cddr">
    <xsl:param name="l"/>
    <xsl:call-template name="cdr">
      <xsl:with-param name="l">
        <xsl:call-template name="cdr">
          <xsl:with-param name="l" select="$l"/>
        </xsl:call-template>
      </xsl:with-param>
    </xsl:call-template>
  </xsl:template>

  <xsl:template name="third">
    <xsl:param name="l"/>
    <xsl:call-template name="car">
      <xsl:with-param name="l">
        <xsl:call-template name="cddr">
          <xsl:with-param name="l" select="$l"/>
        </xsl:call-template>
      </xsl:with-param>
    </xsl:call-template>
  </xsl:template>

  <xsl:template name="cdddr">
    <xsl:param name="l"/>
    <xsl:call-template name="cdr">
      <xsl:with-param name="l">
        <xsl:call-template name="cddr">
          <xsl:with-param name="l" select="$l"/>
        </xsl:call-template>
      </xsl:with-param>
    </xsl:call-template>
  </xsl:template>
  <!-- poor man's 0-based integer arrays (integer is non-negative and four digits long now) -->
  <!-- the biggest identifier number is 1061 for jordan7 in MML 758 -->
  <xsl:param name="int_size">
    <xsl:text>4</xsl:text>
  </xsl:param>

  <!-- #index must be 0-based -->
  <xsl:template name="arr_ref">
    <xsl:param name="array"/>
    <xsl:param name="index"/>
    <xsl:variable name="beg" select="$int_size * $index"/>
    <xsl:value-of select="number(substring($array, $beg, $beg + $int_size))"/>
  </xsl:template>

  <xsl:template name="apush">
    <xsl:param name="array"/>
    <xsl:param name="obj"/>
    <xsl:variable name="obj1">
      <xsl:call-template name="arr_pad_obj">
        <xsl:with-param name="obj"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:value-of select="concat($array, $obj1)"/>
  </xsl:template>

  <xsl:template name="arr_set">
    <xsl:param name="array"/>
    <xsl:param name="index"/>
    <xsl:param name="obj"/>
    <xsl:variable name="obj1">
      <xsl:call-template name="arr_pad_obj">
        <xsl:with-param name="obj"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:variable name="beg" select="$int_size * $index"/>
    <xsl:variable name="end" select="$beg + $int_size"/>
    <xsl:variable name="prefix" select="substring($array, 0, $beg)"/>
    <xsl:variable name="postfix" select="substring($array, $end)"/>
    <xsl:value-of select="concat($prefix, $obj1, $postfix)"/>
  </xsl:template>

  <!-- explicit for speed -->
  <xsl:template name="arr_zeros">
    <xsl:param name="l"/>
    <xsl:choose>
      <xsl:when test="$l = 0">
        <xsl:text/>
      </xsl:when>
      <xsl:when test="$l = 1">
        <xsl:text>0</xsl:text>
      </xsl:when>
      <xsl:when test="$l = 2">
        <xsl:text>00</xsl:text>
      </xsl:when>
      <xsl:when test="$l = 3">
        <xsl:text>000</xsl:text>
      </xsl:when>
      <xsl:when test="$l = 4">
        <xsl:text>0000</xsl:text>
      </xsl:when>
      <xsl:when test="$l = 5">
        <xsl:text>00000</xsl:text>
      </xsl:when>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="arr_pad_obj">
    <xsl:param name="obj"/>
    <xsl:variable name="length" select="$int_size - string-length($obj)"/>
    <xsl:variable name="padding">
      <xsl:call-template name="arr_zeros">
        <xsl:with-param name="l" select="$length"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:value-of select="concat($padding, $obj)"/>
  </xsl:template>

  <!-- List utilities -->
  <xsl:template name="list">
    <xsl:param name="separ"/>
    <xsl:param name="elems"/>
    <xsl:for-each select="$elems">
      <xsl:apply-templates select="."/>
      <xsl:if test="not(position()=last())">
        <xsl:value-of select="$separ"/>
      </xsl:if>
    </xsl:for-each>
  </xsl:template>

  <!-- List utility with additional arg - now only used for formula lists -->
  <xsl:template name="ilist">
    <xsl:param name="separ"/>
    <xsl:param name="elems"/>
    <xsl:param name="i"/>
    <xsl:param name="pr"/>
    <xsl:for-each select="$elems">
      <xsl:apply-templates select=".">
        <xsl:with-param name="i" select="$i"/>
        <xsl:with-param name="pr" select="$pr"/>
      </xsl:apply-templates>
      <xsl:if test="not(position()=last())">
        <xsl:value-of select="$separ"/>
      </xsl:if>
    </xsl:for-each>
  </xsl:template>

  <!-- newlined list -->
  <xsl:template name="nlist">
    <xsl:param name="separ"/>
    <xsl:param name="elems"/>
    <xsl:for-each select="$elems">
      <xsl:apply-templates select="."/>
      <xsl:if test="not(position()=last())">
        <xsl:element name="br"/>
        <xsl:value-of select="$separ"/>
      </xsl:if>
    </xsl:for-each>
  </xsl:template>

  <!-- newlined andlist -->
  <xsl:template name="andlist">
    <xsl:param name="elems"/>
    <xsl:for-each select="$elems">
      <xsl:apply-templates select="."/>
      <xsl:if test="not(position()=last())">
        <xsl:element name="b">
          <xsl:text>and </xsl:text>
        </xsl:element>
        <xsl:element name="br"/>
      </xsl:if>
    </xsl:for-each>
  </xsl:template>

  <xsl:template name="dlist">
    <xsl:param name="separ"/>
    <xsl:param name="elems"/>
    <xsl:for-each select="$elems">
      <xsl:element name="div">
        <xsl:apply-templates select="."/>
        <xsl:if test="not(position()=last())">
          <xsl:value-of select="$separ"/>
        </xsl:if>
      </xsl:element>
    </xsl:for-each>
  </xsl:template>

  <!-- Pretty print constants with their types. -->
  <!-- This now assumes that all #elems are Typ. -->
  <!-- For subseries of consts with the same Typ, -->
  <!-- the Typ is printed only once. -->
  <!-- #sep2 is now either "be " or "being ", -->
  <!-- comma is added automatically. -->
  <!-- #pl passes proolevel if after addabsrefs processing -->
  <!-- (needed for const_links) -->
  <xsl:template name="jtlist">
    <xsl:param name="j"/>
    <xsl:param name="sep2"/>
    <xsl:param name="elems"/>
    <xsl:param name="pl"/>
    <xsl:variable name="addpl">
      <xsl:if test="$const_links&gt;0">
        <xsl:call-template name="addp">
          <xsl:with-param name="pl" select="$pl"/>
        </xsl:call-template>
      </xsl:if>
    </xsl:variable>
    <xsl:for-each select="$elems">
      <xsl:variable name="nr1" select="$j+position()"/>
      <xsl:if test="$const_links&gt;0">
        <xsl:element name="a">
          <xsl:attribute name="NAME">
            <xsl:value-of select="concat(&quot;c&quot;,$nr1,$addpl)"/>
          </xsl:attribute>
        </xsl:element>
      </xsl:if>
      <xsl:call-template name="ppconst">
        <xsl:with-param name="nr" select="$nr1"/>
        <xsl:with-param name="vid" select="@vid"/>
      </xsl:call-template>
      <xsl:choose>
        <xsl:when test="position()=last()">
          <xsl:value-of select="$sep2"/>
          <xsl:apply-templates select="."/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:variable name="eq1">
            <xsl:call-template name="are_equal_vid">
              <xsl:with-param name="el1" select="."/>
              <xsl:with-param name="el2" select="following-sibling::*[1]"/>
            </xsl:call-template>
          </xsl:variable>
          <xsl:if test="$eq1=&quot;0&quot;">
            <xsl:value-of select="$sep2"/>
            <xsl:apply-templates select="."/>
          </xsl:if>
          <xsl:text>, </xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <!-- translate constructor (notation) kinds to their mizar/mmlquery names -->
  <xsl:template name="mkind">
    <xsl:param name="kind"/>
    <xsl:choose>
      <xsl:when test="$kind = &apos;M&apos;">
        <xsl:text>mode</xsl:text>
      </xsl:when>
      <xsl:when test="$kind = &apos;V&apos;">
        <xsl:text>attr</xsl:text>
      </xsl:when>
      <xsl:when test="$kind = &apos;R&apos;">
        <xsl:text>pred</xsl:text>
      </xsl:when>
      <xsl:when test="$kind = &apos;K&apos;">
        <xsl:text>func</xsl:text>
      </xsl:when>
      <xsl:when test="$kind = &apos;G&apos;">
        <xsl:text>aggr</xsl:text>
      </xsl:when>
      <xsl:when test="$kind = &apos;L&apos;">
        <xsl:text>struct</xsl:text>
      </xsl:when>
      <xsl:when test="$kind = &apos;U&apos;">
        <xsl:text>sel</xsl:text>
      </xsl:when>
    </xsl:choose>
  </xsl:template>

  <!-- translate reference kinds to their mizar/mmlquery names -->
  <xsl:template name="refkind">
    <xsl:param name="kind"/>
    <xsl:choose>
      <xsl:when test="$kind = &apos;T&apos;">
        <xsl:text>th</xsl:text>
      </xsl:when>
      <xsl:when test="$kind = &apos;D&apos;">
        <xsl:text>def</xsl:text>
      </xsl:when>
      <xsl:when test="$kind = &apos;S&apos;">
        <xsl:text>sch</xsl:text>
      </xsl:when>
    </xsl:choose>
  </xsl:template>

  <!-- return first symbol corresponding to a constructor ($,$nr); -->
  <!-- sometimes we know the $pid or even the formatnr ($fnr) precisely; -->
  <!-- if nothing found, just concat #k and #nr; #r says to look for -->
  <!-- right bracket instead of left or fail if the format is not bracket -->
  <xsl:template name="abs1">
    <xsl:param name="k"/>
    <xsl:param name="nr"/>
    <xsl:param name="r"/>
    <xsl:param name="fnr"/>
    <xsl:param name="pid"/>
    <!-- DEBUG    "abs1:"; $k; ":"; $fnr; ":"; -->
    <xsl:variable name="fnr1">
      <xsl:choose>
        <xsl:when test="$fnr">
          <xsl:value-of select="$fnr"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:call-template name="formt_nr">
            <xsl:with-param name="k" select="$k"/>
            <xsl:with-param name="nr" select="$nr"/>
            <xsl:with-param name="pid" select="$pid"/>
          </xsl:call-template>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:for-each select="document($formats,/)">
      <xsl:choose>
        <xsl:when test="not(key(&apos;F&apos;,$fnr1))">
          <xsl:value-of select="concat($k,$nr)"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:for-each select="key(&apos;F&apos;,$fnr1)">
            <xsl:variable name="snr" select="@symbolnr"/>
            <xsl:variable name="sk1" select="@kind"/>
            <xsl:variable name="sk">
              <xsl:choose>
                <xsl:when test="$sk1=&quot;L&quot;">
                  <xsl:text>G</xsl:text>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:value-of select="$sk1"/>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:variable>
            <xsl:variable name="dkey" select="concat(&apos;D_&apos;,$sk)"/>
            <xsl:variable name="rsnr">
              <xsl:if test="$sk=&apos;K&apos;">
                <xsl:value-of select="@rightsymbolnr"/>
              </xsl:if>
            </xsl:variable>
            <!-- return nothing if right bracket of nonbracket symbol is asked -->
            <!-- shouldn't it be an error? -->
            <xsl:if test="not($r=&apos;1&apos;) or ($sk=&apos;K&apos;)">
              <xsl:for-each select="document($vocs,/)">
                <xsl:choose>
                  <xsl:when test="key($dkey,$snr)">
                    <xsl:for-each select="key($dkey,$snr)">
                      <xsl:choose>
                        <xsl:when test="($sk=&apos;K&apos;) and ($r=&apos;1&apos;)">
                          <xsl:for-each select="key(&apos;D_L&apos;,$rsnr)">
                            <xsl:value-of select="@name"/>
                          </xsl:for-each>
                        </xsl:when>
                        <xsl:otherwise>
                          <xsl:value-of select="@name"/>
                        </xsl:otherwise>
                      </xsl:choose>
                    </xsl:for-each>
                  </xsl:when>
                  <!-- try the built-in symbols -->
                  <xsl:otherwise>
                    <xsl:choose>
                      <xsl:when test="($snr=&apos;1&apos;) and ($sk=&apos;M&apos;)">
                        <xsl:text>set</xsl:text>
                      </xsl:when>
                      <xsl:when test="($snr=&apos;1&apos;) and ($sk=&apos;R&apos;)">
                        <xsl:text>=</xsl:text>
                      </xsl:when>
                      <xsl:when test="($snr=&apos;1&apos;) and ($sk=&apos;K&apos;)">
                        <xsl:choose>
                          <xsl:when test="$r=&apos;1&apos;">
                            <xsl:text>]</xsl:text>
                          </xsl:when>
                          <xsl:otherwise>
                            <xsl:text>[</xsl:text>
                          </xsl:otherwise>
                        </xsl:choose>
                      </xsl:when>
                      <xsl:when test="($snr=&apos;2&apos;) and ($sk=&apos;K&apos;)">
                        <xsl:choose>
                          <xsl:when test="$r=&apos;1&apos;">
                            <xsl:text>}</xsl:text>
                          </xsl:when>
                          <xsl:otherwise>
                            <xsl:text>{</xsl:text>
                          </xsl:otherwise>
                        </xsl:choose>
                      </xsl:when>
                      <xsl:otherwise>
                        <xsl:value-of select="concat($k,$nr)"/>
                      </xsl:otherwise>
                    </xsl:choose>
                  </xsl:otherwise>
                </xsl:choose>
              </xsl:for-each>
            </xsl:if>
          </xsl:for-each>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <!-- private for abs1 -->
  <xsl:template name="formt_nr">
    <xsl:param name="k"/>
    <xsl:param name="nr"/>
    <xsl:param name="pid"/>
    <xsl:call-template name="car">
      <xsl:with-param name="l">
        <xsl:call-template name="patt_info">
          <xsl:with-param name="k" select="$k"/>
          <xsl:with-param name="nr" select="$nr"/>
          <xsl:with-param name="pid" select="$pid"/>
        </xsl:call-template>
      </xsl:with-param>
    </xsl:call-template>
  </xsl:template>

  <!-- private for patt_info -->
  <xsl:template name="mk_vis_list">
    <xsl:param name="els"/>
    <xsl:for-each select="$els">
      <xsl:value-of select="@x"/>
      <xsl:text>:</xsl:text>
    </xsl:for-each>
  </xsl:template>

  <!-- private for patt_info - -->
  <!-- assumes we already are inside the right pattern -->
  <xsl:template name="encode_std_pattern">
    <xsl:param name="k"/>
    <xsl:variable name="shift0">
      <xsl:choose>
        <xsl:when test="@antonymic">
          <xsl:text>1</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="shift">
      <xsl:choose>
        <xsl:when test="($k=&quot;V&quot;) and (@kind=&quot;R&quot;)">
          <xsl:value-of select="2 + $shift0"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="$shift0"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="plink">
      <xsl:choose>
        <xsl:when test="@redefnr&gt;0">
          <xsl:text>1</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="vis">
      <xsl:call-template name="mk_vis_list">
        <xsl:with-param name="els" select="Visible/Int"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:call-template name="cons">
      <xsl:with-param name="h" select="@formatnr"/>
      <xsl:with-param name="t">
        <xsl:call-template name="cons">
          <xsl:with-param name="h" select="$shift"/>
          <xsl:with-param name="t">
            <xsl:call-template name="cons">
              <xsl:with-param name="h" select="$plink"/>
              <xsl:with-param name="t" select="$vis"/>
            </xsl:call-template>
          </xsl:with-param>
        </xsl:call-template>
      </xsl:with-param>
    </xsl:call-template>
  </xsl:template>

  <!-- this is a small hack to minimize chasing patterns -->
  <!-- returns list [formatnr, antonymic or expandable (+2 if attrpred), -->
  <!-- redefinition | visiblelist] -->
  <xsl:template name="patt_info">
    <xsl:param name="k"/>
    <xsl:param name="nr"/>
    <xsl:param name="pid"/>
    <xsl:variable name="k1">
      <xsl:choose>
        <xsl:when test="$k=&quot;L&quot;">
          <xsl:text>G</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="$k"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="typ" select="($k1 = &quot;G&quot;) or ($k1=&quot;M&quot;)"/>
    <xsl:variable name="pkey" select="concat(&apos;P_&apos;,$k1)"/>
    <xsl:choose>
      <xsl:when test="$pid&gt;0">
        <xsl:variable name="doc">
          <xsl:choose>
            <xsl:when test="($typ and key(&apos;EXP&apos;,$pid)) 
		     or (key($pkey,$nr)[$pid=@relnr])">
              <xsl:text/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:value-of select="$patts"/>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:for-each select="document($doc,/)">
          <xsl:choose>
            <xsl:when test="$typ and key(&apos;EXP&apos;,$pid)">
              <xsl:for-each select="key(&apos;EXP&apos;,$pid)">
                <xsl:variable name="vis">
                  <xsl:call-template name="mk_vis_list">
                    <xsl:with-param name="els" select="Visible/Int"/>
                  </xsl:call-template>
                </xsl:variable>
                <xsl:call-template name="cons">
                  <xsl:with-param name="h" select="@formatnr"/>
                  <xsl:with-param name="t">
                    <xsl:call-template name="cons">
                      <xsl:with-param name="h">
                        <xsl:text>1</xsl:text>
                      </xsl:with-param>
                      <xsl:with-param name="t">
                        <xsl:call-template name="cons">
                          <xsl:with-param name="h">
                            <xsl:text>0</xsl:text>
                          </xsl:with-param>
                          <xsl:with-param name="t" select="$vis"/>
                        </xsl:call-template>
                      </xsl:with-param>
                    </xsl:call-template>
                  </xsl:with-param>
                </xsl:call-template>
              </xsl:for-each>
            </xsl:when>
            <xsl:otherwise>
              <xsl:choose>
                <xsl:when test="key($pkey,$nr)[$pid=@relnr]">
                  <xsl:for-each select="key($pkey,$nr)[$pid=@relnr]">
                    <xsl:call-template name="encode_std_pattern">
                      <xsl:with-param name="k" select="$k"/>
                    </xsl:call-template>
                  </xsl:for-each>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:text>failedpid:</xsl:text>
                  <xsl:value-of select="$k1"/>
                  <xsl:text>:</xsl:text>
                  <xsl:value-of select="$nr"/>
                  <xsl:text>:</xsl:text>
                  <xsl:value-of select="$pid"/>
                  <xsl:text>:</xsl:text>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:for-each>
      </xsl:when>
      <xsl:otherwise>
        <xsl:variable name="doc">
          <xsl:choose>
            <xsl:when test="key($pkey,$nr)">
              <xsl:text/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:value-of select="$patts"/>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:for-each select="document($doc,/)">
          <xsl:for-each select="key($pkey,$nr)[position()=1]">
            <xsl:call-template name="encode_std_pattern">
              <xsl:with-param name="k" select="$k"/>
            </xsl:call-template>
          </xsl:for-each>
        </xsl:for-each>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- the string length #ls does not change; -->
  <!-- test if the #n-th position in #pl from back is underscore, -->
  <!-- if so, cut it and what follows it, -->
  <!-- otherwise try with n+1 -->
  <!-- called externally with #n=1; -->
  <!-- $n<10 is probably needed to guard the recursion - limits us -->
  <!-- to nine digit numbers of previous blocks - seems safe now -->
  <xsl:template name="get_parent_level">
    <xsl:param name="pl"/>
    <xsl:param name="ls"/>
    <xsl:param name="n"/>
    <xsl:variable name="p">
      <xsl:value-of select="$ls - $n"/>
    </xsl:variable>
    <xsl:variable name="p1">
      <xsl:value-of select="$ls - ($n + 1)"/>
    </xsl:variable>
    <xsl:choose>
      <xsl:when test="substring($pl, $p, 1) = &apos;_&apos;">
        <xsl:value-of select="substring($pl, 1, $p1)"/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:if test="$n &lt; 10">
          <xsl:call-template name="get_parent_level">
            <xsl:with-param name="pl" select="$pl"/>
            <xsl:with-param name="ls" select="$ls"/>
            <xsl:with-param name="n" select="$n+1"/>
          </xsl:call-template>
        </xsl:if>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="add_hs_attrs">
    <xsl:attribute name="class">
      <xsl:text>txt</xsl:text>
    </xsl:attribute>
    <xsl:attribute name="onclick">
      <xsl:text>hs(this)</xsl:text>
    </xsl:attribute>
    <xsl:attribute name="href">
      <xsl:text>javascript:()</xsl:text>
    </xsl:attribute>
  </xsl:template>

  <xsl:template name="add_hs2_attrs">
    <xsl:attribute name="class">
      <xsl:text>txt</xsl:text>
    </xsl:attribute>
    <xsl:attribute name="onclick">
      <xsl:text>hs2(this)</xsl:text>
    </xsl:attribute>
    <xsl:attribute name="href">
      <xsl:text>javascript:()</xsl:text>
    </xsl:attribute>
  </xsl:template>

  <xsl:template name="add_hsNdiv_attrs">
    <xsl:attribute name="class">
      <xsl:text>txt</xsl:text>
    </xsl:attribute>
    <xsl:attribute name="onclick">
      <xsl:text>hsNdiv(this)</xsl:text>
    </xsl:attribute>
    <xsl:attribute name="href">
      <xsl:text>javascript:()</xsl:text>
    </xsl:attribute>
  </xsl:template>

  <xsl:template name="add_ajax_attrs">
    <xsl:param name="u"/>
    <xsl:attribute name="class">
      <xsl:text>txt</xsl:text>
    </xsl:attribute>
    <xsl:attribute name="onclick">
      <xsl:value-of select="concat(&quot;makeRequest(this,&apos;&quot;,$u,&quot;&apos;)&quot;)"/>
    </xsl:attribute>
    <xsl:attribute name="href">
      <xsl:text>javascript:()</xsl:text>
    </xsl:attribute>
  </xsl:template>

  <!--  -->
  <!-- File: frmtrm.xsltxt - html-ization of Mizar XML, code for terms, formulas, and types -->
  <!--  -->
  <!-- Author: Josef Urban -->
  <!--  -->
  <!-- License: GPL (GNU GENERAL PUBLIC LICENSE) -->
  <!-- Formulas -->
  <!-- #i is nr of the bound variable, 0 by default -->
  <!-- #k is start of the sequence of vars with the same type, $i by default -->
  <!-- we now output only one typing for such sequences -->
  <!-- #ex tells that we should print it as existential statement, -->
  <!-- i.e. also omitting the first descending Not (the caller -->
  <!-- should guarantee that there _is_ a Not after the block of For-s) -->
  <!-- #pr tells to put the formula in paranthesis -->
  <xsl:template match="For">
    <xsl:param name="i"/>
    <xsl:param name="k"/>
    <xsl:param name="ex"/>
    <xsl:param name="pr"/>
    <xsl:variable name="j">
      <xsl:choose>
        <xsl:when test="$i">
          <xsl:value-of select="$i"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="l">
      <xsl:choose>
        <xsl:when test="$k">
          <xsl:value-of select="$k"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="$j"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:if test="$l = $j">
      <!-- print initial quantifier if at the beginning of var segment -->
      <xsl:if test="$pr">
        <xsl:text>( </xsl:text>
      </xsl:if>
      <xsl:choose>
        <xsl:when test="$ex=&quot;1&quot;">
          <xsl:text> ex </xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>for </xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:if>
    <xsl:call-template name="pqvar">
      <xsl:with-param name="nr" select="$j + 1"/>
      <xsl:with-param name="vid" select="@vid"/>
    </xsl:call-template>
    <xsl:variable name="nm">
      <xsl:value-of select="name(*[2])"/>
    </xsl:variable>
    <xsl:variable name="eq1">
      <xsl:choose>
        <xsl:when test="($nm = &quot;For&quot;) and (*[1]/@nr = *[2]/*[1]/@nr)">
          <xsl:call-template name="are_equal">
            <xsl:with-param name="el1" select="*[1]"/>
            <xsl:with-param name="el2" select="*[2]/*[1]"/>
          </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:choose>
      <xsl:when test="$eq1=&quot;1&quot;">
        <xsl:text>, </xsl:text>
        <xsl:apply-templates select="*[2]">
          <xsl:with-param name="i" select="$j+1"/>
          <xsl:with-param name="k" select="$l"/>
          <xsl:with-param name="ex" select="$ex"/>
          <xsl:with-param name="pr" select="$pr"/>
        </xsl:apply-templates>
      </xsl:when>
      <xsl:otherwise>
        <xsl:choose>
          <xsl:when test="$ex=&quot;1&quot;">
            <xsl:text> being</xsl:text>
            <xsl:apply-templates select="*[1]">
              <xsl:with-param name="i" select="$j + 1"/>
            </xsl:apply-templates>
            <xsl:choose>
              <xsl:when test="$nm = &quot;For&quot;">
                <xsl:apply-templates select="*[2]">
                  <xsl:with-param name="i" select="$j+1"/>
                  <xsl:with-param name="ex" select="$ex"/>
                </xsl:apply-templates>
              </xsl:when>
              <xsl:otherwise>
                <xsl:text> st </xsl:text>
                <!-- $nm; -->
                <xsl:if test="($nm = &quot;And&quot;) or (name(Not/*[1]) = &quot;And&quot;) or (name(Not/*[1]) = &quot;For&quot;)">
                  <xsl:element name="br"/>
                </xsl:if>
                <xsl:apply-templates select="Not/*[1]">
                  <xsl:with-param name="i" select="$j+1"/>
                </xsl:apply-templates>
                <xsl:choose>
                  <xsl:when test="Pred|PrivPred|Is|Verum|ErrorFrm">
                    <!-- " PREDFOR "; -->
                    <xsl:apply-templates select="*[2]">
                      <xsl:with-param name="i" select="$j+1"/>
                      <xsl:with-param name="not">
                        <xsl:text>1</xsl:text>
                      </xsl:with-param>
                    </xsl:apply-templates>
                  </xsl:when>
                  <!-- for antonymous Preds -->
                  <xsl:otherwise>
                    <xsl:if test="And">
                      <xsl:text>( </xsl:text>
                      <xsl:choose>
                        <xsl:when test="And[@pid=$pid_Or_And]">
                          <xsl:for-each select="*[2]/*">
                            <xsl:if test="position()&gt;1">
                              <xsl:text> or </xsl:text>
                            </xsl:if>
                            <xsl:variable name="neg1">
                              <xsl:call-template name="is_negative">
                                <xsl:with-param name="el" select="."/>
                              </xsl:call-template>
                            </xsl:variable>
                            <xsl:choose>
                              <xsl:when test="$neg1 = &quot;1&quot;">
                                <xsl:choose>
                                  <xsl:when test="name() = &quot;Not&quot;">
                                    <xsl:apply-templates select="*[1]">
                                      <xsl:with-param name="i" select="$j+1"/>
                                    </xsl:apply-templates>
                                  </xsl:when>
                                  <!-- now Pred, which is antonymous -->
                                  <xsl:otherwise>
                                    <xsl:apply-templates select=".">
                                      <xsl:with-param name="i" select="$j+1"/>
                                      <xsl:with-param name="not">
                                        <xsl:text>1</xsl:text>
                                      </xsl:with-param>
                                    </xsl:apply-templates>
                                  </xsl:otherwise>
                                </xsl:choose>
                              </xsl:when>
                              <xsl:otherwise>
                                <xsl:choose>
                                  <xsl:when test="name() = &quot;For&quot;">
                                    <xsl:apply-templates select=".">
                                      <xsl:with-param name="i" select="$j+1"/>
                                      <xsl:with-param name="ex">
                                        <xsl:text>1</xsl:text>
                                      </xsl:with-param>
                                    </xsl:apply-templates>
                                  </xsl:when>
                                  <xsl:otherwise>
                                    <xsl:text> not </xsl:text>
                                    <xsl:apply-templates select=".">
                                      <xsl:with-param name="i" select="$j+1"/>
                                    </xsl:apply-templates>
                                  </xsl:otherwise>
                                </xsl:choose>
                              </xsl:otherwise>
                            </xsl:choose>
                          </xsl:for-each>
                        </xsl:when>
                        <xsl:otherwise>
                          <!-- pretend this is an impl -->
                          <xsl:call-template name="ilist">
                            <xsl:with-param name="separ">
                              <xsl:text> &amp; </xsl:text>
                            </xsl:with-param>
                            <xsl:with-param name="elems" select="*[2]/*[position()&lt;last()]"/>
                            <xsl:with-param name="i" select="$j+1"/>
                            <xsl:with-param name="pr">
                              <xsl:text>1</xsl:text>
                            </xsl:with-param>
                          </xsl:call-template>
                          <xsl:text> implies </xsl:text>
                          <xsl:choose>
                            <xsl:when test="*[2]/*[@pid=$pid_Impl_RightNot]">
                              <xsl:apply-templates select="*[2]/*[@pid=$pid_Impl_RightNot]/*[1]">
                                <xsl:with-param name="i" select="$j+1"/>
                              </xsl:apply-templates>
                            </xsl:when>
                            <xsl:when test="name(*[2]/*[position()=last()]) = &quot;For&quot;">
                              <xsl:apply-templates select="*[2]/*[position()=last()]">
                                <xsl:with-param name="i" select="$j+1"/>
                                <xsl:with-param name="ex">
                                  <xsl:text>1</xsl:text>
                                </xsl:with-param>
                              </xsl:apply-templates>
                            </xsl:when>
                            <xsl:otherwise>
                              <xsl:variable name="neg1">
                                <xsl:call-template name="is_negative">
                                  <xsl:with-param name="el" select="*[2]/*[position()=last()]"/>
                                </xsl:call-template>
                              </xsl:variable>
                              <xsl:choose>
                                <xsl:when test="$neg1 = &quot;1&quot;">
                                  <xsl:choose>
                                    <xsl:when test="name(*[2]/*[position()=last()]) = &quot;Not&quot;">
                                      <xsl:apply-templates select="*[2]/*[position()=last()]/*[1]">
                                        <xsl:with-param name="i" select="$j+1"/>
                                      </xsl:apply-templates>
                                    </xsl:when>
                                    <!-- now Pred, which is antonymous -->
                                    <xsl:otherwise>
                                      <xsl:apply-templates select="*[2]/*[position()=last()]">
                                        <xsl:with-param name="i" select="$j+1"/>
                                        <xsl:with-param name="not">
                                          <xsl:text>1</xsl:text>
                                        </xsl:with-param>
                                      </xsl:apply-templates>
                                    </xsl:otherwise>
                                  </xsl:choose>
                                </xsl:when>
                                <xsl:otherwise>
                                  <xsl:text> not </xsl:text>
                                  <xsl:apply-templates select="*[2]/*[position()=last()]">
                                    <xsl:with-param name="i" select="$j+1"/>
                                  </xsl:apply-templates>
                                </xsl:otherwise>
                              </xsl:choose>
                            </xsl:otherwise>
                          </xsl:choose>
                        </xsl:otherwise>
                      </xsl:choose>
                      <xsl:text> )</xsl:text>
                    </xsl:if>
                  </xsl:otherwise>
                </xsl:choose>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:when>
          <xsl:otherwise>
            <xsl:text> being</xsl:text>
            <xsl:apply-templates select="*[1]">
              <xsl:with-param name="i" select="$j + 1"/>
            </xsl:apply-templates>
            <xsl:if test="not(($nm = &quot;For&quot;) or ($nm=&quot;Not&quot;))">
              <xsl:text> holds </xsl:text>
            </xsl:if>
            <xsl:if test="($nm = &quot;And&quot;) or ($nm=&quot;For&quot;)">
              <xsl:element name="br"/>
            </xsl:if>
            <xsl:choose>
              <xsl:when test="$nm=&quot;Not&quot;">
                <xsl:text> </xsl:text>
                <xsl:apply-templates select="*[2]">
                  <xsl:with-param name="i" select="$j+1"/>
                  <xsl:with-param name="st">
                    <xsl:text>1</xsl:text>
                  </xsl:with-param>
                </xsl:apply-templates>
              </xsl:when>
              <xsl:otherwise>
                <xsl:text> </xsl:text>
                <xsl:apply-templates select="*[2]">
                  <xsl:with-param name="i" select="$j+1"/>
                </xsl:apply-templates>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:otherwise>
        </xsl:choose>
        <xsl:if test="$pr">
          <xsl:text> )</xsl:text>
        </xsl:if>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- tpl [And/For] { <div {"for B being"; apply[*[1]]; -->
  <!-- " holds "; <div { @class="add";  apply[*[2]]; } } } -->
  <!-- return 1 if this is a Not-ended sequence of For-s -->
  <xsl:template name="check_for_not">
    <xsl:param name="el"/>
    <xsl:choose>
      <xsl:when test="(name($el)=&quot;Not&quot;) or (name($el)=&quot;Pred&quot;)">
        <xsl:call-template name="is_negative">
          <xsl:with-param name="el" select="$el"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:choose>
          <xsl:when test="(name($el)=&quot;And&quot;) and (($el/@pid = $pid_Or_And) or ($el/@pid = $pid_Impl_And))">
            <xsl:text>1</xsl:text>
          </xsl:when>
          <xsl:otherwise>
            <xsl:choose>
              <xsl:when test="name($el)=&quot;For&quot;">
                <xsl:call-template name="check_for_not">
                  <xsl:with-param name="el" select="$el/*[2]"/>
                </xsl:call-template>
              </xsl:when>
              <xsl:otherwise>
                <xsl:text>0</xsl:text>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="Not">
    <xsl:param name="i"/>
    <xsl:param name="pr"/>
    <xsl:param name="st"/>
    <xsl:variable name="fnb">
      <xsl:choose>
        <xsl:when test="For">
          <xsl:call-template name="check_for_not">
            <xsl:with-param name="el" select="*[1]/*[2]"/>
          </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:choose>
      <xsl:when test="$fnb=&quot;1&quot;">
        <xsl:apply-templates select="*[1]">
          <xsl:with-param name="i" select="$i"/>
          <xsl:with-param name="ex">
            <xsl:text>1</xsl:text>
          </xsl:with-param>
        </xsl:apply-templates>
      </xsl:when>
      <xsl:otherwise>
        <xsl:choose>
          <xsl:when test="Pred|Is|PrivPred|Verum|ErrorFrm">
            <xsl:if test="$st=&quot;1&quot;">
              <xsl:text> holds </xsl:text>
            </xsl:if>
            <xsl:apply-templates select="*[1]">
              <xsl:with-param name="i" select="$i"/>
              <xsl:with-param name="not">
                <xsl:text>1</xsl:text>
              </xsl:with-param>
            </xsl:apply-templates>
          </xsl:when>
          <xsl:otherwise>
            <xsl:variable name="i3">
              <xsl:call-template name="is_impl1">
                <xsl:with-param name="el" select="."/>
              </xsl:call-template>
            </xsl:variable>
            <xsl:choose>
              <xsl:when test="$i3 &gt; 0">
                <!-- " IMPL1 "; $i3; -->
                <xsl:choose>
                  <xsl:when test="$st=&quot;1&quot;">
                    <xsl:text> st </xsl:text>
                  </xsl:when>
                  <xsl:otherwise>
                    <xsl:text>( </xsl:text>
                  </xsl:otherwise>
                </xsl:choose>
                <xsl:choose>
                  <xsl:when test="$i3=2">
                    <xsl:call-template name="ilist">
                      <xsl:with-param name="separ">
                        <xsl:text> &amp; </xsl:text>
                      </xsl:with-param>
                      <xsl:with-param name="elems" select="*[1]/*[not(@pid=$pid_Impl_RightNot)]"/>
                      <xsl:with-param name="i" select="$i"/>
                      <xsl:with-param name="pr">
                        <xsl:text>1</xsl:text>
                      </xsl:with-param>
                    </xsl:call-template>
                    <xsl:choose>
                      <xsl:when test="$st=&quot;1&quot;">
                        <xsl:text> holds </xsl:text>
                        <xsl:element name="br"/>
                      </xsl:when>
                      <xsl:otherwise>
                        <xsl:text> implies </xsl:text>
                      </xsl:otherwise>
                    </xsl:choose>
                    <xsl:apply-templates select="*[1]/*[@pid=$pid_Impl_RightNot]/*[1]">
                      <xsl:with-param name="i" select="$i"/>
                    </xsl:apply-templates>
                  </xsl:when>
                  <xsl:otherwise>
                    <xsl:call-template name="ilist">
                      <xsl:with-param name="separ">
                        <xsl:text> &amp; </xsl:text>
                      </xsl:with-param>
                      <xsl:with-param name="elems" select="*[1]/*[position()&lt;last()]"/>
                      <xsl:with-param name="i" select="$i"/>
                      <xsl:with-param name="pr">
                        <xsl:text>1</xsl:text>
                      </xsl:with-param>
                    </xsl:call-template>
                    <xsl:choose>
                      <xsl:when test="$st=&quot;1&quot;">
                        <xsl:text> holds </xsl:text>
                        <xsl:element name="br"/>
                      </xsl:when>
                      <xsl:otherwise>
                        <xsl:text> implies </xsl:text>
                      </xsl:otherwise>
                    </xsl:choose>
                    <xsl:choose>
                      <xsl:when test="$i3=3">
                        <xsl:choose>
                          <xsl:when test="name(*[1]/*[position()=last()]) = &quot;Not&quot;">
                            <xsl:apply-templates select="*[1]/*[position()=last()]/*[1]">
                              <xsl:with-param name="i" select="$i"/>
                            </xsl:apply-templates>
                          </xsl:when>
                          <!-- now Pred, which is antonymous -->
                          <xsl:otherwise>
                            <xsl:apply-templates select="*[1]/*[position()=last()]">
                              <xsl:with-param name="i" select="$i"/>
                              <xsl:with-param name="not">
                                <xsl:text>1</xsl:text>
                              </xsl:with-param>
                            </xsl:apply-templates>
                          </xsl:otherwise>
                        </xsl:choose>
                      </xsl:when>
                      <xsl:when test="$i3=4">
                        <xsl:apply-templates select="*[1]/*[position()=last()]">
                          <xsl:with-param name="i" select="$i"/>
                          <xsl:with-param name="ex">
                            <xsl:text>1</xsl:text>
                          </xsl:with-param>
                        </xsl:apply-templates>
                      </xsl:when>
                      <xsl:when test="$i3=5">
                        <xsl:text> not </xsl:text>
                        <xsl:apply-templates select="*[1]/*[position()=last()]">
                          <xsl:with-param name="i" select="$i"/>
                        </xsl:apply-templates>
                      </xsl:when>
                    </xsl:choose>
                  </xsl:otherwise>
                </xsl:choose>
                <xsl:if test="not($st=&quot;1&quot;)">
                  <xsl:text> )</xsl:text>
                </xsl:if>
              </xsl:when>
              <xsl:otherwise>
                <xsl:if test="$st=&quot;1&quot;">
                  <xsl:text> holds </xsl:text>
                  <xsl:element name="br"/>
                </xsl:if>
                <xsl:variable name="i1_1">
                  <xsl:call-template name="is_or1">
                    <xsl:with-param name="el" select="."/>
                  </xsl:call-template>
                </xsl:variable>
                <xsl:variable name="i1">
                  <xsl:choose>
                    <xsl:when test="$i1_1=&quot;1&quot;">
                      <xsl:text>1</xsl:text>
                    </xsl:when>
                    <xsl:otherwise>
                      <!-- artifficially system-constructed complex fla, try some reconstruction -->
                      <xsl:choose>
                        <xsl:when test="not(@pid) and (name(*[1])=&quot;And&quot;) and (count(*[1]/*)&gt;=2)">
                          <xsl:text>1</xsl:text>
                        </xsl:when>
                        <xsl:otherwise>
                          <xsl:text>0</xsl:text>
                        </xsl:otherwise>
                      </xsl:choose>
                    </xsl:otherwise>
                  </xsl:choose>
                </xsl:variable>
                <xsl:choose>
                  <xsl:when test="$i1=&quot;1&quot;">
                    <xsl:text>( </xsl:text>
                    <!-- " OR1 "; -->
                    <xsl:for-each select="*[1]/*">
                      <xsl:if test="position()&gt;1">
                        <xsl:text> or </xsl:text>
                      </xsl:if>
                      <xsl:variable name="neg1">
                        <xsl:call-template name="is_negative">
                          <xsl:with-param name="el" select="."/>
                        </xsl:call-template>
                      </xsl:variable>
                      <xsl:choose>
                        <xsl:when test="$neg1 = &quot;1&quot;">
                          <xsl:choose>
                            <xsl:when test="name() = &quot;Not&quot;">
                              <xsl:apply-templates select="*[1]">
                                <xsl:with-param name="i" select="$i"/>
                              </xsl:apply-templates>
                            </xsl:when>
                            <!-- now Pred, which is antonymous -->
                            <xsl:otherwise>
                              <xsl:apply-templates select=".">
                                <xsl:with-param name="i" select="$i"/>
                                <xsl:with-param name="not">
                                  <xsl:text>1</xsl:text>
                                </xsl:with-param>
                              </xsl:apply-templates>
                            </xsl:otherwise>
                          </xsl:choose>
                        </xsl:when>
                        <xsl:otherwise>
                          <xsl:choose>
                            <xsl:when test="name() = &quot;For&quot;">
                              <xsl:apply-templates select=".">
                                <xsl:with-param name="i" select="$i"/>
                                <xsl:with-param name="ex">
                                  <xsl:text>1</xsl:text>
                                </xsl:with-param>
                              </xsl:apply-templates>
                            </xsl:when>
                            <xsl:otherwise>
                              <xsl:text> not </xsl:text>
                              <xsl:apply-templates select=".">
                                <xsl:with-param name="i" select="$i"/>
                              </xsl:apply-templates>
                            </xsl:otherwise>
                          </xsl:choose>
                        </xsl:otherwise>
                      </xsl:choose>
                    </xsl:for-each>
                    <xsl:text> )</xsl:text>
                  </xsl:when>
                  <xsl:otherwise>
                    <xsl:text>not </xsl:text>
                    <xsl:if test="@pid">
                      <xsl:comment>
                        <xsl:text>HUMANRECFAILED</xsl:text>
                      </xsl:comment>
                    </xsl:if>
                    <!-- else {"NOPID  ";} -->
                    <xsl:apply-templates select="*[1]">
                      <xsl:with-param name="i" select="$i"/>
                    </xsl:apply-templates>
                  </xsl:otherwise>
                </xsl:choose>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- this was too AI, mizar is much simpler -->
  <!-- $cnt=`count(*[1]/*)`; -->
  <!-- $pcnt1 = { if [$i3="1"] { count_positive(#els=`*[1]/*`,#nr=$cnt); } else {"10000";} } -->
  <!-- $pcnt = $pcnt1; -->
  <!-- // $pcnt1; ":"; $cnt; ":"; $i3; -->
  <!-- if [($pcnt>0) and ($pcnt<$cnt)] { -->
  <!-- // "hhhhhhhhhhhh"; -->
  <!-- "( "; put_positive(#separ=" & ",#els=`*[1]/*`,#nr=$pcnt,#i=$i); " implies "; -->
  <!-- put_positive(#separ=" or ",#els=`*[1]/*`,#nr=`$cnt - $pcnt`,#neg="1",#i=$i); ")"; -->
  <!-- } -->
  <!-- else { if [($i3="1") and ($pcnt=0)] { "( "; put_positive(#separ=" or ",#els=`*[1]/*`,#nr=$cnt,#neg="1",#i=$i); ")"; } -->
  <!-- if [$i3="1"  and (*[1]/*[not(name()="Not")]) and (*[1]/Not)] { "( ( "; -->
  <!-- ilist(#separ=" & ", #elems=`*[1]/*[not(name()="Not")]`, #i=$i,#pr="1"); -->
  <!-- " )"; " implies "; -->
  <!-- "( "; ilist(#separ=" or ", #elems=`*[1]/Not/*[1]`, #i=$i,#pr="1"); " ) )"; } -->
  <xsl:template match="And">
    <xsl:param name="i"/>
    <xsl:param name="pr"/>
    <xsl:variable name="e1">
      <xsl:call-template name="is_equiv">
        <xsl:with-param name="el" select="."/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:choose>
      <xsl:when test="$e1=&quot;1&quot;">
        <xsl:text>( </xsl:text>
        <xsl:apply-templates select="*[1]/*[1]/*[1]">
          <xsl:with-param name="i" select="$i"/>
          <xsl:with-param name="pr">
            <xsl:text>1</xsl:text>
          </xsl:with-param>
        </xsl:apply-templates>
        <xsl:text> iff </xsl:text>
        <xsl:apply-templates select="*[1]/*[1]/*[2]/*[1]">
          <xsl:with-param name="i" select="$i"/>
        </xsl:apply-templates>
        <xsl:text> )</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <!-- a bit risky -->
        <xsl:choose>
          <xsl:when test="(@pid=$pid_Iff) and (count(*)=2)">
            <xsl:variable name="i1">
              <xsl:call-template name="is_impl">
                <xsl:with-param name="el" select="*[1]"/>
              </xsl:call-template>
            </xsl:variable>
            <xsl:choose>
              <xsl:when test="$i1=&quot;1&quot;">
                <xsl:text>( </xsl:text>
                <xsl:apply-templates select="*[1]/*[1]/*[1]">
                  <xsl:with-param name="i" select="$i"/>
                  <xsl:with-param name="pr">
                    <xsl:text>1</xsl:text>
                  </xsl:with-param>
                </xsl:apply-templates>
                <xsl:text> iff </xsl:text>
                <xsl:apply-templates select="*[1]/*[1]/*[2]/*[1]">
                  <xsl:with-param name="i" select="$i"/>
                </xsl:apply-templates>
                <xsl:text> )</xsl:text>
              </xsl:when>
              <xsl:otherwise>
                <xsl:variable name="i2">
                  <xsl:call-template name="is_impl">
                    <xsl:with-param name="el" select="*[2]"/>
                  </xsl:call-template>
                </xsl:variable>
                <xsl:choose>
                  <xsl:when test="$i2=&quot;1&quot;">
                    <xsl:text>( </xsl:text>
                    <xsl:apply-templates select="*[2]/*[1]/*[2]/*[1]">
                      <xsl:with-param name="i" select="$i"/>
                      <xsl:with-param name="pr">
                        <xsl:text>1</xsl:text>
                      </xsl:with-param>
                    </xsl:apply-templates>
                    <xsl:text> iff </xsl:text>
                    <xsl:apply-templates select="*[2]/*[1]/*[1]">
                      <xsl:with-param name="i" select="$i"/>
                    </xsl:apply-templates>
                    <xsl:text> )</xsl:text>
                  </xsl:when>
                  <xsl:otherwise>
                    <xsl:variable name="i3">
                      <xsl:call-template name="is_impl1">
                        <xsl:with-param name="el" select="*[1]"/>
                      </xsl:call-template>
                    </xsl:variable>
                    <xsl:variable name="i4">
                      <xsl:call-template name="is_impl1">
                        <xsl:with-param name="el" select="*[2]"/>
                      </xsl:call-template>
                    </xsl:variable>
                    <xsl:choose>
                      <xsl:when test="($i3 &gt; 0) or ($i4 &gt; 0)">
                        <!-- select better impl - no, prefer the first -->
                        <xsl:variable name="which">
                          <xsl:choose>
                            <xsl:when test="($i3 = 0)">
                              <xsl:text>2</xsl:text>
                            </xsl:when>
                            <xsl:otherwise>
                              <xsl:text>1</xsl:text>
                            </xsl:otherwise>
                          </xsl:choose>
                        </xsl:variable>
                        <!-- if [($i4 = 0)] { "1"; } else { -->
                        <!-- if [$i3 > $i4] { "2"; } else { "1"; }}}} -->
                        <xsl:variable name="i5">
                          <xsl:choose>
                            <xsl:when test="$which=1">
                              <xsl:value-of select="$i3"/>
                            </xsl:when>
                            <xsl:otherwise>
                              <xsl:value-of select="$i4"/>
                            </xsl:otherwise>
                          </xsl:choose>
                        </xsl:variable>
                        <xsl:for-each select="*[position()=$which]">
                          <!-- " IFF2: "; $which; -->
                          <xsl:text>( </xsl:text>
                          <xsl:choose>
                            <xsl:when test="$i5=2">
                              <xsl:call-template name="ilist">
                                <xsl:with-param name="separ">
                                  <xsl:text> &amp; </xsl:text>
                                </xsl:with-param>
                                <xsl:with-param name="elems" select="*[1]/*[not(@pid=$pid_Impl_RightNot)]"/>
                                <xsl:with-param name="i" select="$i"/>
                                <xsl:with-param name="pr">
                                  <xsl:text>1</xsl:text>
                                </xsl:with-param>
                              </xsl:call-template>
                              <xsl:text> iff </xsl:text>
                              <xsl:apply-templates select="*[1]/*[@pid=$pid_Impl_RightNot]/*[1]">
                                <xsl:with-param name="i" select="$i"/>
                              </xsl:apply-templates>
                            </xsl:when>
                            <xsl:otherwise>
                              <xsl:call-template name="ilist">
                                <xsl:with-param name="separ">
                                  <xsl:text> &amp; </xsl:text>
                                </xsl:with-param>
                                <xsl:with-param name="elems" select="*[1]/*[position()&lt;last()]"/>
                                <xsl:with-param name="i" select="$i"/>
                                <xsl:with-param name="pr">
                                  <xsl:text>1</xsl:text>
                                </xsl:with-param>
                              </xsl:call-template>
                              <xsl:text> iff </xsl:text>
                              <xsl:choose>
                                <xsl:when test="$i5=3">
                                  <xsl:choose>
                                    <xsl:when test="name(*[1]/*[position()=last()]) = &quot;Not&quot;">
                                      <xsl:apply-templates select="*[1]/*[position()=last()]/*[1]">
                                        <xsl:with-param name="i" select="$i"/>
                                      </xsl:apply-templates>
                                    </xsl:when>
                                    <!-- now Pred, which is antonymous -->
                                    <xsl:otherwise>
                                      <xsl:apply-templates select="*[1]/*[position()=last()]">
                                        <xsl:with-param name="i" select="$i"/>
                                        <xsl:with-param name="not">
                                          <xsl:text>1</xsl:text>
                                        </xsl:with-param>
                                      </xsl:apply-templates>
                                    </xsl:otherwise>
                                  </xsl:choose>
                                </xsl:when>
                                <xsl:when test="$i5=4">
                                  <xsl:apply-templates select="*[1]/*[position()=last()]">
                                    <xsl:with-param name="i" select="$i"/>
                                    <xsl:with-param name="ex">
                                      <xsl:text>1</xsl:text>
                                    </xsl:with-param>
                                  </xsl:apply-templates>
                                </xsl:when>
                                <xsl:when test="$i5=5">
                                  <xsl:text> not </xsl:text>
                                  <xsl:apply-templates select="*[1]/*[position()=last()]">
                                    <xsl:with-param name="i" select="$i"/>
                                  </xsl:apply-templates>
                                </xsl:when>
                              </xsl:choose>
                            </xsl:otherwise>
                          </xsl:choose>
                          <xsl:text> )</xsl:text>
                        </xsl:for-each>
                      </xsl:when>
                      <xsl:otherwise>
                        <xsl:text>( </xsl:text>
                        <xsl:comment>
                          <xsl:text>HUMANRECFAILED</xsl:text>
                        </xsl:comment>
                        <xsl:call-template name="ilist">
                          <xsl:with-param name="separ">
                            <xsl:text> &amp; </xsl:text>
                          </xsl:with-param>
                          <xsl:with-param name="elems" select="*"/>
                          <xsl:with-param name="i" select="$i"/>
                          <xsl:with-param name="pr">
                            <xsl:text>1</xsl:text>
                          </xsl:with-param>
                        </xsl:call-template>
                        <xsl:text> )</xsl:text>
                      </xsl:otherwise>
                    </xsl:choose>
                  </xsl:otherwise>
                </xsl:choose>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:when>
          <xsl:otherwise>
            <xsl:text>( </xsl:text>
            <!-- if[not(@pid)] { " NOPID ";} -->
            <xsl:call-template name="ilist">
              <xsl:with-param name="separ">
                <xsl:text> &amp; </xsl:text>
              </xsl:with-param>
              <xsl:with-param name="elems" select="*"/>
              <xsl:with-param name="i" select="$i"/>
              <xsl:with-param name="pr">
                <xsl:text>1</xsl:text>
              </xsl:with-param>
            </xsl:call-template>
            <xsl:text> )</xsl:text>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="Pred">
    <xsl:param name="i"/>
    <xsl:param name="not"/>
    <xsl:param name="pr"/>
    <xsl:choose>
      <xsl:when test="@kind=&apos;P&apos;">
        <xsl:call-template name="pschpvar">
          <xsl:with-param name="nr" select="@nr"/>
        </xsl:call-template>
        <xsl:text>[</xsl:text>
        <xsl:call-template name="ilist">
          <xsl:with-param name="separ">
            <xsl:text>,</xsl:text>
          </xsl:with-param>
          <xsl:with-param name="elems" select="*"/>
          <xsl:with-param name="i" select="$i"/>
        </xsl:call-template>
        <xsl:text>]</xsl:text>
      </xsl:when>
      <xsl:when test="(@kind=&apos;V&apos;) or (@kind=&apos;R&apos;)">
        <xsl:variable name="pi">
          <xsl:call-template name="patt_info">
            <xsl:with-param name="k" select="@kind"/>
            <xsl:with-param name="nr" select="@nr"/>
            <xsl:with-param name="pid" select="@pid"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:variable name="fnr">
          <xsl:call-template name="car">
            <xsl:with-param name="l" select="$pi"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:variable name="antonym">
          <xsl:call-template name="cadr">
            <xsl:with-param name="l" select="$pi"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:variable name="plink">
          <xsl:call-template name="third">
            <xsl:with-param name="l" select="$pi"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:variable name="pid">
          <xsl:choose>
            <xsl:when test="$plink=&quot;1&quot;">
              <xsl:value-of select="@pid"/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:text>0</xsl:text>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:variable name="predattr">
          <xsl:choose>
            <xsl:when test="$antonym&gt;1">
              <xsl:text>1</xsl:text>
            </xsl:when>
            <xsl:otherwise>
              <xsl:text>0</xsl:text>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:variable name="neg">
          <xsl:choose>
            <xsl:when test="$not=&quot;1&quot;">
              <xsl:value-of select="($antonym + $not) mod 2"/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:value-of select="$antonym mod 2"/>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:if test="$neg=&quot;1&quot;">
          <xsl:text>not </xsl:text>
        </xsl:if>
        <xsl:choose>
          <xsl:when test="(@kind=&apos;V&apos;) and ($predattr=&quot;0&quot;)">
            <xsl:apply-templates select="*[position() = last()]">
              <xsl:with-param name="i" select="$i"/>
            </xsl:apply-templates>
            <xsl:text> is </xsl:text>
            <xsl:call-template name="abs">
              <xsl:with-param name="k" select="@kind"/>
              <xsl:with-param name="nr" select="@nr"/>
              <xsl:with-param name="sym">
                <xsl:call-template name="abs1">
                  <xsl:with-param name="k" select="@kind"/>
                  <xsl:with-param name="nr" select="@nr"/>
                  <xsl:with-param name="fnr" select="$fnr"/>
                  <xsl:with-param name="pid" select="$pid"/>
                </xsl:call-template>
              </xsl:with-param>
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <xsl:call-template name="pp">
              <xsl:with-param name="k" select="@kind"/>
              <xsl:with-param name="nr" select="@nr"/>
              <xsl:with-param name="args" select="*"/>
              <xsl:with-param name="pid" select="@pid"/>
              <xsl:with-param name="i" select="$i"/>
            </xsl:call-template>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
    </xsl:choose>
  </xsl:template>

  <!-- ,#sym1=abs(#k=`@kind`, #nr=`@nr`, #sym=abs1(#k=`@kind`, #nr=`@nr`))); }} -->
  <!-- "[ "; list(#separ=",", #elems=`*`); "]"; } -->
  <xsl:template match="PrivPred">
    <xsl:param name="i"/>
    <xsl:param name="pr"/>
    <xsl:param name="not"/>
    <xsl:if test="$not=&quot;1&quot;">
      <xsl:text> not </xsl:text>
    </xsl:if>
    <xsl:call-template name="pppred">
      <xsl:with-param name="nr" select="@nr"/>
    </xsl:call-template>
    <xsl:text>[</xsl:text>
    <xsl:call-template name="ilist">
      <xsl:with-param name="separ">
        <xsl:text>,</xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="*[position() &lt; last()]"/>
      <xsl:with-param name="i" select="$i"/>
    </xsl:call-template>
    <xsl:text>]</xsl:text>
  </xsl:template>

  <xsl:template match="Is">
    <xsl:param name="i"/>
    <xsl:param name="pr"/>
    <xsl:param name="not"/>
    <xsl:apply-templates select="*[1]">
      <xsl:with-param name="i" select="$i"/>
    </xsl:apply-templates>
    <xsl:text> is </xsl:text>
    <xsl:if test="$not=&quot;1&quot;">
      <xsl:text> not </xsl:text>
    </xsl:if>
    <xsl:apply-templates select="*[2]">
      <xsl:with-param name="i" select="$i"/>
    </xsl:apply-templates>
  </xsl:template>

  <xsl:template match="Verum">
    <xsl:param name="i"/>
    <xsl:param name="pr"/>
    <xsl:param name="not"/>
    <xsl:choose>
      <xsl:when test="$not=&quot;1&quot;">
        <xsl:text>contradiction</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>verum</xsl:text>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="ErrorFrm">
    <xsl:param name="i"/>
    <xsl:param name="pr"/>
    <xsl:param name="not"/>
    <xsl:if test="$not=&quot;1&quot;">
      <xsl:text> not </xsl:text>
    </xsl:if>
    <xsl:text>errorfrm</xsl:text>
  </xsl:template>

  <!-- Terms -->
  <!-- #p is the parenthesis count -->
  <!-- #i is the size of the var stack -->
  <xsl:template match="Var">
    <xsl:param name="p"/>
    <xsl:param name="i"/>
    <xsl:choose>
      <xsl:when test="$print_identifiers &gt; 0">
        <xsl:variable name="vid">
          <xsl:call-template name="get_vid">
            <xsl:with-param name="up" select="$i - @nr"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:call-template name="pqvar">
          <xsl:with-param name="nr" select="@nr"/>
          <xsl:with-param name="vid" select="$vid"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="pvar">
          <xsl:with-param name="nr" select="@nr"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- search parent For and Fraenkel for #nr, return its vid -->
  <!-- #bound says how many vars ( -1) are currently quantified -->
  <!-- (depth of the quantifier stack), so we need to go -->
  <!-- #bound - #nr times up (this is now passed just as #up) -->
  <xsl:template name="get_vid">
    <xsl:param name="up"/>
    <xsl:choose>
      <xsl:when test="name() = &quot;For&quot;">
        <xsl:choose>
          <xsl:when test="$up = &quot;0&quot;">
            <xsl:value-of select="@vid"/>
          </xsl:when>
          <xsl:otherwise>
            <xsl:for-each select="..">
              <xsl:call-template name="get_vid">
                <xsl:with-param name="up" select="$up - 1"/>
              </xsl:call-template>
            </xsl:for-each>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
      <xsl:otherwise>
        <xsl:choose>
          <xsl:when test="(name() = &quot;Typ&quot;) and (name(..) = &quot;Fraenkel&quot;)">
            <!-- the case for var inside fraenkel typ - -->
            <!-- only previous lamdaargs are available -->
            <xsl:variable name="tnr" select="count(preceding-sibling::Typ)"/>
            <xsl:choose>
              <xsl:when test="$up &lt; $tnr">
                <xsl:value-of select="preceding-sibling::Typ[position() = (last() - $up)]/@vid"/>
              </xsl:when>
              <xsl:otherwise>
                <xsl:for-each select="../..">
                  <xsl:call-template name="get_vid">
                    <xsl:with-param name="up" select="$up - $tnr"/>
                  </xsl:call-template>
                </xsl:for-each>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:when>
          <xsl:otherwise>
            <xsl:choose>
              <xsl:when test="name() = &quot;Fraenkel&quot;">
                <!-- the case for var inside lambdaterm and lambdaformula - -->
                <!-- all lamdaargs are available -->
                <xsl:variable name="tnr" select="count(Typ)"/>
                <xsl:choose>
                  <xsl:when test="$up &lt; $tnr">
                    <xsl:value-of select="Typ[position() = (last() - $up)]/@vid"/>
                  </xsl:when>
                  <xsl:otherwise>
                    <xsl:for-each select="..">
                      <xsl:call-template name="get_vid">
                        <xsl:with-param name="up" select="$up - $tnr"/>
                      </xsl:call-template>
                    </xsl:for-each>
                  </xsl:otherwise>
                </xsl:choose>
              </xsl:when>
              <xsl:otherwise>
                <xsl:for-each select="..">
                  <xsl:call-template name="get_vid">
                    <xsl:with-param name="up" select="$up"/>
                  </xsl:call-template>
                </xsl:for-each>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- trickery to translate loci to constants and identifiers when needed -->
  <!-- this unfortunately does not work for IdentifyRegistration, so that's -->
  <!-- dealt with by looking at the compatibility fla now :-( -->
  <!-- ###TODO: also the constructor types -->
  <xsl:template match="LocusVar">
    <xsl:param name="p"/>
    <xsl:param name="i"/>
    <!-- try definienda possibly containing "it" -->
    <xsl:choose>
      <xsl:when test="($mml=&quot;0&quot;) and (ancestor::DefMeaning)">
        <xsl:variable name="it_possible">
          <xsl:choose>
            <xsl:when test="(ancestor::Definiens[(@constrkind=&quot;M&quot;) or (@constrkind=&quot;K&quot;)])">
              <xsl:text>1</xsl:text>
            </xsl:when>
            <xsl:otherwise>
              <xsl:text>0</xsl:text>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:variable name="maxnr">
          <xsl:for-each select="ancestor::Definiens">
            <xsl:value-of select="count(Typ)"/>
          </xsl:for-each>
        </xsl:variable>
        <xsl:choose>
          <xsl:when test="(@nr = $maxnr) and ($it_possible=&quot;1&quot;)">
            <xsl:element name="b">
              <xsl:text>it</xsl:text>
            </xsl:element>
          </xsl:when>
          <xsl:otherwise>
            <xsl:choose>
              <xsl:when test="@nr &lt;= $maxnr">
                <xsl:variable name="nr" select="@nr"/>
                <!-- preceding-sibling written this way selects in reverse document order -->
                <xsl:for-each select="ancestor::Definiens">
                  <xsl:variable name="argtypes" select="preceding-sibling::DefinitionBlock[1]/Let/Typ"/>
                  <xsl:call-template name="ppconst">
                    <xsl:with-param name="nr" select="$nr"/>
                    <xsl:with-param name="vid" select="$argtypes[position() = $nr]/@vid"/>
                  </xsl:call-template>
                </xsl:for-each>
              </xsl:when>
              <xsl:otherwise>
                <xsl:call-template name="ploci">
                  <xsl:with-param name="nr" select="@nr"/>
                </xsl:call-template>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
      <xsl:otherwise>
        <!-- note that the Constructor may come from different document here -->
        <!-- even if $mml = 0, but that can be handled above, because this is -->
        <!-- only used for result types which in that case shouldn't have changed -->
        <!-- Exapnsion used for expandable mode defs -->
        <xsl:choose>
          <xsl:when test="($mml=&quot;0&quot;) and ((ancestor::Constructor) or (ancestor::Expansion)) and (ancestor::Definition)">
            <xsl:variable name="nr" select="@nr"/>
            <xsl:variable name="argtypes" select="ancestor::DefinitionBlock/Let/Typ"/>
            <xsl:call-template name="ppconst">
              <xsl:with-param name="nr" select="$nr"/>
              <xsl:with-param name="vid" select="$argtypes[position() = $nr]/@vid"/>
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <xsl:choose>
              <xsl:when test="($mml=&quot;0&quot;) and (ancestor::Registration)">
                <xsl:variable name="nr" select="@nr"/>
                <xsl:variable name="argtypes" select="ancestor::RegistrationBlock/Let/Typ"/>
                <xsl:call-template name="ppconst">
                  <xsl:with-param name="nr" select="$nr"/>
                  <xsl:with-param name="vid" select="$argtypes[position() = $nr]/@vid"/>
                </xsl:call-template>
              </xsl:when>
              <xsl:otherwise>
                <xsl:choose>
                  <xsl:when test="($mml=&quot;0&quot;) and ((ancestor::DefPred) or (ancestor::DefFunc))">
                    <xsl:text>$</xsl:text>
                    <xsl:value-of select="@nr"/>
                  </xsl:when>
                  <xsl:otherwise>
                    <xsl:call-template name="ploci">
                      <xsl:with-param name="nr" select="@nr"/>
                    </xsl:call-template>
                  </xsl:otherwise>
                </xsl:choose>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="FreeVar">
    <xsl:param name="p"/>
    <xsl:param name="i"/>
    <xsl:text>X</xsl:text>
    <xsl:value-of select="@nr"/>
  </xsl:template>

  <xsl:template match="Const">
    <xsl:param name="p"/>
    <xsl:param name="i"/>
    <xsl:choose>
      <xsl:when test="($print_identifiers &gt; 0)  and ((@vid&gt;0) or ($proof_links&gt;0))">
        <xsl:choose>
          <xsl:when test="@vid &gt; 0">
            <xsl:variable name="pl">
              <xsl:if test="$const_links=2">
                <xsl:call-template name="get_nearest_level">
                  <xsl:with-param name="el" select=".."/>
                </xsl:call-template>
              </xsl:if>
            </xsl:variable>
            <xsl:call-template name="ppconst">
              <xsl:with-param name="nr" select="@nr"/>
              <xsl:with-param name="vid" select="@vid"/>
              <xsl:with-param name="pl" select="$pl"/>
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <xsl:variable name="pl">
              <xsl:call-template name="get_nearest_level">
                <xsl:with-param name="el" select=".."/>
              </xsl:call-template>
            </xsl:variable>
            <xsl:call-template name="absconst">
              <xsl:with-param name="nr" select="@nr"/>
              <xsl:with-param name="pl" select="$pl"/>
            </xsl:call-template>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="pconst">
          <xsl:with-param name="nr" select="@nr"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="InfConst">
    <xsl:param name="p"/>
    <xsl:param name="i"/>
    <xsl:text>D</xsl:text>
    <xsl:value-of select="@nr"/>
  </xsl:template>

  <xsl:template match="Num">
    <xsl:param name="p"/>
    <xsl:param name="i"/>
    <xsl:value-of select="@nr"/>
  </xsl:template>

  <xsl:template match="Func">
    <xsl:param name="p"/>
    <xsl:param name="i"/>
    <xsl:choose>
      <xsl:when test="@kind=&apos;F&apos;">
        <xsl:call-template name="pschfvar">
          <xsl:with-param name="nr" select="@nr"/>
        </xsl:call-template>
        <xsl:text>(</xsl:text>
        <xsl:call-template name="ilist">
          <xsl:with-param name="separ">
            <xsl:text>,</xsl:text>
          </xsl:with-param>
          <xsl:with-param name="elems" select="*"/>
          <xsl:with-param name="i" select="$i"/>
        </xsl:call-template>
        <xsl:text>)</xsl:text>
      </xsl:when>
      <xsl:when test="@kind=&apos;U&apos;">
        <xsl:text>the </xsl:text>
        <xsl:call-template name="abs">
          <xsl:with-param name="k" select="@kind"/>
          <xsl:with-param name="nr" select="@nr"/>
          <xsl:with-param name="sym">
            <xsl:call-template name="abs1">
              <xsl:with-param name="k" select="@kind"/>
              <xsl:with-param name="nr" select="@nr"/>
            </xsl:call-template>
          </xsl:with-param>
        </xsl:call-template>
        <xsl:text> of </xsl:text>
        <xsl:apply-templates select="*[position() = last()]">
          <xsl:with-param name="p" select="$p"/>
          <xsl:with-param name="i" select="$i"/>
        </xsl:apply-templates>
      </xsl:when>
      <xsl:otherwise>
        <xsl:variable name="par">
          <xsl:choose>
            <xsl:when test="$p&gt;0">
              <xsl:value-of select="$p+1"/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:choose>
                <xsl:when test="name(..)=&apos;Func&apos;">
                  <xsl:text>1</xsl:text>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:text>0</xsl:text>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:call-template name="pp">
          <xsl:with-param name="k" select="@kind"/>
          <xsl:with-param name="nr" select="@nr"/>
          <xsl:with-param name="args" select="*"/>
          <xsl:with-param name="parenth" select="$par"/>
          <xsl:with-param name="pid" select="@pid"/>
          <xsl:with-param name="i" select="$i"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="PrivFunc">
    <xsl:param name="p"/>
    <xsl:param name="i"/>
    <xsl:call-template name="ppfunc">
      <xsl:with-param name="nr" select="@nr"/>
    </xsl:call-template>
    <xsl:text>(</xsl:text>
    <xsl:call-template name="ilist">
      <xsl:with-param name="separ">
        <xsl:text>,</xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="*[position()&gt;1]"/>
      <xsl:with-param name="i" select="$i"/>
    </xsl:call-template>
    <xsl:text>)</xsl:text>
  </xsl:template>

  <xsl:template match="ErrorTrm">
    <xsl:param name="p"/>
    <xsl:param name="i"/>
    <xsl:text>errortrm</xsl:text>
  </xsl:template>

  <xsl:template match="Fraenkel">
    <xsl:param name="p"/>
    <xsl:param name="i"/>
    <xsl:variable name="j">
      <xsl:choose>
        <xsl:when test="$i">
          <xsl:value-of select="$i"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="par">
      <xsl:choose>
        <xsl:when test="$p&gt;0">
          <xsl:value-of select="$p+1"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>1</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="inc">
      <xsl:value-of select="count(*) - 2"/>
    </xsl:variable>
    <!-- number of vars introduced here -->
    <xsl:variable name="paren_color" select="$par mod $pcolors_nr"/>
    <xsl:element name="span">
      <xsl:attribute name="class">
        <xsl:value-of select="concat(&quot;p&quot;,$paren_color)"/>
      </xsl:attribute>
      <xsl:text>{</xsl:text>
      <xsl:element name="span">
        <xsl:attribute name="class">
          <xsl:text>default</xsl:text>
        </xsl:attribute>
        <xsl:text> </xsl:text>
        <!-- first display the term -->
        <xsl:apply-templates select="*[position() = last() - 1]">
          <xsl:with-param name="p" select="$par"/>
          <xsl:with-param name="i" select="$j + $inc"/>
        </xsl:apply-templates>
        <!-- then the var types -->
        <xsl:if test="count(*)&gt;2">
          <xsl:text> where </xsl:text>
          <xsl:for-each select="*[position() &lt; last() - 1]">
            <xsl:call-template name="pqvar">
              <xsl:with-param name="nr" select="$j + position()"/>
              <xsl:with-param name="vid" select="@vid"/>
            </xsl:call-template>
            <xsl:variable name="eq1">
              <xsl:choose>
                <xsl:when test="position()=last()">
                  <xsl:text>0</xsl:text>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:call-template name="are_equal_vid">
                    <xsl:with-param name="el1" select="."/>
                    <xsl:with-param name="el2" select="following-sibling::*[1]"/>
                  </xsl:call-template>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:variable>
            <xsl:if test="$eq1=&quot;0&quot;">
              <xsl:text> is </xsl:text>
              <xsl:apply-templates select=".">
                <xsl:with-param name="i" select="$j + position() - 1"/>
              </xsl:apply-templates>
            </xsl:if>
            <xsl:if test="not(position()=last())">
              <xsl:text>, </xsl:text>
            </xsl:if>
          </xsl:for-each>
        </xsl:if>
        <!-- then the formula -->
        <xsl:text> : </xsl:text>
        <xsl:apply-templates select="*[position() = last()]">
          <xsl:with-param name="i" select="$j + $inc"/>
        </xsl:apply-templates>
        <xsl:text> </xsl:text>
      </xsl:element>
      <xsl:text>}</xsl:text>
    </xsl:element>
    <xsl:text> </xsl:text>
  </xsl:template>

  <!-- Types -->
  <!-- element Typ { -->
  <!-- attribute kind { "M" | "G" | "L" | "errortyp" }, -->
  <!-- attribute nr { xsd:integer }?, -->
  <!-- ( attribute absnr { xsd:integer }, -->
  <!-- attribute aid { xsd:string } )?, -->
  <!-- attribute pid { xsd:integer }?, -->
  <!-- Cluster*, -->
  <!-- Term* -->
  <!-- } -->
  <xsl:template match="Typ">
    <xsl:param name="i"/>
    <xsl:text> </xsl:text>
    <xsl:if test="count(*)&gt;0">
      <xsl:apply-templates select="*[1]">
        <xsl:with-param name="i" select="$i"/>
      </xsl:apply-templates>
    </xsl:if>
    <xsl:choose>
      <xsl:when test="(@kind=&quot;M&quot;) or (@kind=&quot;G&quot;) or (@kind=&quot;L&quot;)">
        <xsl:variable name="pi">
          <xsl:call-template name="patt_info">
            <xsl:with-param name="k" select="@kind"/>
            <xsl:with-param name="nr" select="@nr"/>
            <xsl:with-param name="pid" select="@pid"/>
          </xsl:call-template>
        </xsl:variable>
        <!-- DEBUG ":"; `@pid`; ":"; $pi; ":"; -->
        <xsl:variable name="fnr">
          <xsl:call-template name="car">
            <xsl:with-param name="l" select="$pi"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:variable name="expand">
          <xsl:call-template name="cadr">
            <xsl:with-param name="l" select="$pi"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:variable name="plink">
          <xsl:call-template name="third">
            <xsl:with-param name="l" select="$pi"/>
          </xsl:call-template>
        </xsl:variable>
        <xsl:variable name="k1">
          <xsl:choose>
            <xsl:when test="@kind = &quot;M&quot;">
              <xsl:text>M</xsl:text>
            </xsl:when>
            <xsl:otherwise>
              <xsl:text>L</xsl:text>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:choose>
          <xsl:when test="($expand=&quot;0&quot;) or not(@pid)">
            <xsl:call-template name="pp">
              <xsl:with-param name="k" select="$k1"/>
              <xsl:with-param name="nr" select="@nr"/>
              <xsl:with-param name="args" select="*[not(name()=&quot;Cluster&quot;)]"/>
              <xsl:with-param name="pid" select="@pid"/>
              <xsl:with-param name="i" select="$i"/>
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <xsl:variable name="sym">
              <xsl:call-template name="abs1">
                <xsl:with-param name="k" select="@kind"/>
                <xsl:with-param name="nr" select="@nr"/>
                <xsl:with-param name="fnr" select="$fnr"/>
              </xsl:call-template>
            </xsl:variable>
            <xsl:variable name="vis">
              <xsl:call-template name="cdddr">
                <xsl:with-param name="l" select="$pi"/>
              </xsl:call-template>
            </xsl:variable>
            <xsl:variable name="el" select="."/>
            <!-- DEBUG ":"; `@pid`; ":"; $pi; ":"; -->
            <xsl:variable name="pid" select="@pid"/>
            <xsl:variable name="doc">
              <xsl:choose>
                <xsl:when test="key(&apos;EXP&apos;,$pid)">
                  <xsl:text/>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:value-of select="$patts"/>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:variable>
            <xsl:variable name="c1">
              <xsl:choose>
                <xsl:when test="($doc = &quot;&quot;) and ($mml = &quot;0&quot;)">
                  <xsl:text>1</xsl:text>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:text>0</xsl:text>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:variable>
            <xsl:for-each select="document($doc,/)">
              <xsl:call-template name="absref">
                <xsl:with-param name="elems" select="key(&apos;EXP&apos;,$pid)"/>
                <xsl:with-param name="c" select="$c1"/>
                <xsl:with-param name="sym" select="$sym"/>
                <xsl:with-param name="pid" select="$pid"/>
              </xsl:call-template>
              <xsl:if test="not($vis = &quot;&quot;)">
                <xsl:text> of </xsl:text>
                <xsl:for-each select="key(&apos;EXP&apos;,$pid)">
                  <xsl:call-template name="descent_many_vis">
                    <xsl:with-param name="patt" select="Expansion/Typ"/>
                    <xsl:with-param name="fix" select="$el"/>
                    <xsl:with-param name="vis" select="Visible/Int"/>
                    <xsl:with-param name="i" select="$i"/>
                  </xsl:call-template>
                </xsl:for-each>
              </xsl:if>
            </xsl:for-each>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
      <xsl:otherwise>
        <xsl:value-of select="@kind"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- gets two Typ, and list of Visible/Int; -->
  <!-- tries to find and print the terms in #fix corresponding -->
  <!-- to the visible loci; #patt is structurally similar to -->
  <!-- #fix, up to the loci -->
  <!-- the handling of #i is potentially incorrect if there is a Fraenkel as -->
  <!-- a param of the type -->
  <xsl:template name="descent_many_vis">
    <xsl:param name="patt"/>
    <xsl:param name="fix"/>
    <xsl:param name="vis"/>
    <xsl:param name="i"/>
    <xsl:if test="$vis">
      <xsl:variable name="v1" select="$vis[position()=1]/@x"/>
      <xsl:variable name="v2" select="$vis[position()&gt;1]"/>
      <!-- DEBUG    "descen:"; $v1; ":"; apply[$patt]; ":"; -->
      <xsl:call-template name="descent_many">
        <xsl:with-param name="patts" select="$patt/*[not(name()=&quot;Cluster&quot;)]"/>
        <xsl:with-param name="fixs" select="$fix/*[not(name()=&quot;Cluster&quot;)]"/>
        <xsl:with-param name="lnr" select="$v1"/>
        <xsl:with-param name="nr" select="count($patt/*[not(name()=&quot;Cluster&quot;)])"/>
        <xsl:with-param name="i" select="$i"/>
      </xsl:call-template>
      <xsl:if test="$v2">
        <xsl:text>,</xsl:text>
        <xsl:call-template name="descent_many_vis">
          <xsl:with-param name="patt" select="$patt"/>
          <xsl:with-param name="fix" select="$fix"/>
          <xsl:with-param name="vis" select="$vis[position()&gt;1]"/>
          <xsl:with-param name="i" select="$i"/>
        </xsl:call-template>
      </xsl:if>
    </xsl:if>
  </xsl:template>

  <xsl:template name="descent_many">
    <xsl:param name="patts"/>
    <xsl:param name="fixs"/>
    <xsl:param name="lnr"/>
    <xsl:param name="nr"/>
    <xsl:param name="i"/>
    <xsl:if test="$nr &gt; 0">
      <xsl:variable name="patt" select="$patts[position()=$nr]"/>
      <xsl:variable name="fix" select="$fixs[position()=$nr]"/>
      <!-- DEBUG "desone:"; $nr; ":"; `name($patt)`; ":"; `name($fix)`; ":"; -->
      <xsl:choose>
        <xsl:when test="(name($patt)=&quot;LocusVar&quot;) and ($patt/@nr=$lnr)">
          <!-- DEBUG    $lnr; ":"; `$patt/@nr`; ":";  "fff"; -->
          <xsl:for-each select="$top">
            <xsl:apply-templates select="$fix">
              <xsl:with-param name="p">
                <xsl:text>0</xsl:text>
              </xsl:with-param>
              <xsl:with-param name="i" select="$i"/>
            </xsl:apply-templates>
          </xsl:for-each>
        </xsl:when>
        <!-- the duplication here is needed to generated the html properly; -->
        <!-- it does not cause any visible slowdown in practice -->
        <xsl:otherwise>
          <xsl:variable name="res">
            <xsl:choose>
              <xsl:when test="name($patt) = name($fix)">
                <xsl:call-template name="descent_many">
                  <xsl:with-param name="patts" select="$patt/*"/>
                  <xsl:with-param name="fixs" select="$fix/*"/>
                  <xsl:with-param name="lnr" select="$lnr"/>
                  <xsl:with-param name="nr" select="count($patt/*)"/>
                  <xsl:with-param name="i" select="$i"/>
                </xsl:call-template>
              </xsl:when>
              <xsl:otherwise>
                <xsl:text/>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:variable>
          <xsl:choose>
            <xsl:when test="$res and not($res=&quot;&quot;)">
              <!-- DEBUG [and contains($res,"fff")] -->
              <xsl:call-template name="descent_many">
                <xsl:with-param name="patts" select="$patt/*"/>
                <xsl:with-param name="fixs" select="$fix/*"/>
                <xsl:with-param name="lnr" select="$lnr"/>
                <xsl:with-param name="nr" select="count($patt/*)"/>
                <xsl:with-param name="i" select="$i"/>
              </xsl:call-template>
            </xsl:when>
            <xsl:otherwise>
              <xsl:call-template name="descent_many">
                <xsl:with-param name="patts" select="$patts"/>
                <xsl:with-param name="fixs" select="$fixs"/>
                <xsl:with-param name="lnr" select="$lnr"/>
                <xsl:with-param name="nr" select="$nr - 1"/>
                <xsl:with-param name="i" select="$i"/>
              </xsl:call-template>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:if>
  </xsl:template>

  <!-- Clusters -->
  <!-- only attributes with pid are now printed, others are results of -->
  <!-- cluster mechanisms - this holds in the current article -->
  <!-- (.xml file) only, environmental files do not have the @pid -->
  <!-- info (yet), so we print everything for them -->
  <xsl:template match="Cluster">
    <xsl:param name="i"/>
    <xsl:choose>
      <xsl:when test="$print_all_attrs = 1">
        <xsl:call-template name="list">
          <xsl:with-param name="separ">
            <xsl:text> </xsl:text>
          </xsl:with-param>
          <xsl:with-param name="elems" select="*"/>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="list">
          <xsl:with-param name="separ">
            <xsl:text> </xsl:text>
          </xsl:with-param>
          <xsl:with-param name="elems" select="*[@pid]"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
    <xsl:text> </xsl:text>
  </xsl:template>

  <!-- Adjective -->
  <!-- element Adjective { -->
  <!-- attribute nr { xsd:integer }, -->
  <!-- attribute value { xsd:boolean }?, -->
  <!-- ( attribute absnr { xsd:integer }, -->
  <!-- attribute aid { xsd:string } )?, -->
  <!-- attribute kind { "V" }?, -->
  <!-- attribute pid { xsd:integer }?, -->
  <!-- Term* -->
  <!-- } -->
  <xsl:template match="Adjective">
    <xsl:param name="i"/>
    <xsl:variable name="pi">
      <xsl:call-template name="patt_info">
        <xsl:with-param name="k">
          <xsl:text>V</xsl:text>
        </xsl:with-param>
        <xsl:with-param name="nr" select="@nr"/>
        <xsl:with-param name="pid" select="@pid"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:variable name="fnr">
      <xsl:call-template name="car">
        <xsl:with-param name="l" select="$pi"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:variable name="anto">
      <xsl:call-template name="cadr">
        <xsl:with-param name="l" select="$pi"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:variable name="plink">
      <xsl:call-template name="third">
        <xsl:with-param name="l" select="$pi"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:variable name="pid">
      <xsl:choose>
        <xsl:when test="$plink=&quot;1&quot;">
          <xsl:value-of select="@pid"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="neg">
      <xsl:choose>
        <xsl:when test="@value=&quot;false&quot;">
          <xsl:value-of select="($anto + 1) mod 2"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="$anto mod 2"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:if test="$neg=&quot;1&quot;">
      <xsl:text>non </xsl:text>
    </xsl:if>
    <xsl:call-template name="abs">
      <xsl:with-param name="k">
        <xsl:text>V</xsl:text>
      </xsl:with-param>
      <xsl:with-param name="nr" select="@nr"/>
      <xsl:with-param name="sym">
        <xsl:call-template name="abs1">
          <xsl:with-param name="k">
            <xsl:text>V</xsl:text>
          </xsl:with-param>
          <xsl:with-param name="nr" select="@nr"/>
          <xsl:with-param name="fnr" select="$fnr"/>
          <xsl:with-param name="pid" select="$pid"/>
        </xsl:call-template>
      </xsl:with-param>
      <xsl:with-param name="pid" select="$pid"/>
    </xsl:call-template>
  </xsl:template>

  <!--  -->
  <!-- File: print_complex.xsltxt - html-ization of Mizar XML, more complex printing stuff -->
  <!--  -->
  <!-- Author: Josef Urban -->
  <!--  -->
  <!-- License: GPL (GNU GENERAL PUBLIC LICENSE) -->
  <!-- ##TODO: try some unification of mkref and absref -->
  <!--  -->
  <!-- theorem, definition and scheme references -->
  <!-- add the reference's href, $c tells if it is from current article -->
  <!-- $nm passes the explicit text to be displayed -->
  <xsl:template name="mkref">
    <xsl:param name="aid"/>
    <xsl:param name="nr"/>
    <xsl:param name="k"/>
    <xsl:param name="c"/>
    <xsl:param name="nm"/>
    <xsl:variable name="mk">
      <xsl:call-template name="refkind">
        <xsl:with-param name="kind" select="$k"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:variable name="alc">
      <xsl:call-template name="lc">
        <xsl:with-param name="s" select="$aid"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:element name="a">
      <xsl:attribute name="class">
        <xsl:text>ref</xsl:text>
      </xsl:attribute>
      <xsl:choose>
        <xsl:when test="($linking = &apos;q&apos;) or (($linking = &apos;m&apos;) and not($c))">
          <xsl:attribute name="href">
            <xsl:value-of select="concat($mmlq,$aid,&quot;:&quot;,$mk,&quot;.&quot;,$nr)"/>
          </xsl:attribute>
        </xsl:when>
        <xsl:otherwise>
          <xsl:attribute name="href">
            <xsl:choose>
              <xsl:when test="($c = 1) and (($linking = &apos;m&apos;) or ($linking = &apos;l&apos;))">
                <xsl:value-of select="concat(&quot;#&quot;,$k, $nr)"/>
              </xsl:when>
              <xsl:otherwise>
                <xsl:value-of select="concat($mizhtml,$alc, &quot;.&quot;,$ext, &quot;#&quot;,$k, $nr)"/>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:attribute>
          <xsl:if test="$c = &quot;1&quot;">
            <xsl:attribute name="target">
              <xsl:text>_self</xsl:text>
            </xsl:attribute>
          </xsl:if>
        </xsl:otherwise>
      </xsl:choose>
      <xsl:if test="$titles=&quot;1&quot;">
        <xsl:attribute name="title">
          <xsl:value-of select="concat($aid,&quot;:&quot;,$mk,&quot;.&quot;,$nr)"/>
        </xsl:attribute>
      </xsl:if>
      <xsl:choose>
        <xsl:when test="$nm">
          <xsl:value-of select="$nm"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="$aid"/>
          <xsl:text>:</xsl:text>
          <xsl:if test="not($k=&quot;T&quot;)">
            <xsl:value-of select="$mk"/>
            <xsl:text> </xsl:text>
          </xsl:if>
          <xsl:value-of select="$nr"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:element>
  </xsl:template>

  <!-- add the constructor/pattern href, $c tells if it is from current article -->
  <!-- #sym is optional Mizar symbol -->
  <!-- #pid links to  patterns instead of constructors -->
  <xsl:template name="absref">
    <xsl:param name="elems"/>
    <xsl:param name="c"/>
    <xsl:param name="sym"/>
    <xsl:param name="pid"/>
    <xsl:variable name="n1">
      <xsl:choose>
        <xsl:when test="($pid &gt; 0)">
          <xsl:text>N</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:for-each select="$elems">
      <xsl:variable name="mk0">
        <xsl:call-template name="mkind">
          <xsl:with-param name="kind" select="@kind"/>
        </xsl:call-template>
      </xsl:variable>
      <xsl:variable name="mk">
        <xsl:choose>
          <xsl:when test="($pid &gt; 0)">
            <xsl:value-of select="concat($mk0, &quot;not&quot;)"/>
          </xsl:when>
          <xsl:otherwise>
            <xsl:value-of select="$mk0"/>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:variable>
      <xsl:variable name="alc">
        <xsl:call-template name="lc">
          <xsl:with-param name="s" select="@aid"/>
        </xsl:call-template>
      </xsl:variable>
      <xsl:element name="a">
        <xsl:choose>
          <xsl:when test="($linking = &apos;q&apos;) or (($linking = &apos;m&apos;) and not($c = &quot;1&quot;))">
            <xsl:attribute name="href">
              <xsl:value-of select="concat($mmlq,@aid,&quot;:&quot;,$mk,&quot;.&quot;,@nr)"/>
            </xsl:attribute>
          </xsl:when>
          <xsl:otherwise>
            <xsl:attribute name="href">
              <xsl:choose>
                <xsl:when test="($c = 1) and (($linking = &apos;m&apos;) or ($linking = &apos;l&apos;))">
                  <xsl:value-of select="concat(&quot;#&quot;, $n1, @kind, @nr)"/>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:value-of select="concat($mizhtml,$alc, &quot;.&quot;,$ext, &quot;#&quot;, $n1, @kind, @nr)"/>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:attribute>
            <!-- this is probably needed if $mml = 1 -->
            <xsl:if test="($c = &quot;1&quot;) and not($linking = &quot;s&quot;)">
              <xsl:attribute name="target">
                <xsl:text>_self</xsl:text>
              </xsl:attribute>
            </xsl:if>
          </xsl:otherwise>
        </xsl:choose>
        <xsl:if test="$titles=&quot;1&quot;">
          <xsl:variable name="t1">
            <xsl:choose>
              <xsl:when test="$pid &gt; 0">
                <xsl:value-of select="@kind"/>
              </xsl:when>
              <xsl:otherwise>
                <xsl:value-of select="$mk"/>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:variable>
          <xsl:attribute name="title">
            <xsl:value-of select="concat(@aid, &quot;:&quot;, $n1, $t1, &quot;.&quot;, @nr)"/>
          </xsl:attribute>
        </xsl:if>
        <xsl:choose>
          <xsl:when test="$sym">
            <xsl:value-of select="$sym"/>
          </xsl:when>
          <xsl:otherwise>
            <xsl:choose>
              <xsl:when test="$relnames &gt; 0">
                <xsl:value-of select="$n1"/>
                <xsl:value-of select="@kind"/>
                <xsl:value-of select="@relnr"/>
              </xsl:when>
              <xsl:otherwise>
                <xsl:value-of select="$n1"/>
                <xsl:value-of select="@kind"/>
                <xsl:value-of select="@nr"/>
                <xsl:text>_</xsl:text>
                <xsl:value-of select="@aid"/>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:element>
    </xsl:for-each>
  </xsl:template>

  <!-- look up and link the constructor/pattern with kind #k and #nr; -->
  <!-- #sym is optionally forces the given Mizar symbol -->
  <!-- #pid links to  patterns instead of constructors -->
  <!-- note that we can be inside a Notation document here already (see pp), -->
  <!-- so the $doc = "" test does not have to mean that we are inside -->
  <!-- the article (could be probably fixed in pp, don't know about expnadable modes though) -->
  <xsl:template name="abs">
    <xsl:param name="k"/>
    <xsl:param name="nr"/>
    <xsl:param name="sym"/>
    <xsl:param name="pid"/>
    <xsl:choose>
      <xsl:when test="$pid&gt;0">
        <xsl:variable name="k1" select="concat(&apos;P_&apos;,$k)"/>
        <xsl:variable name="doc">
          <xsl:choose>
            <xsl:when test="key($k1,$nr)[$pid=@relnr]">
              <xsl:text/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:value-of select="$patts"/>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:for-each select="document($doc,/)">
          <xsl:variable name="c1">
            <xsl:choose>
              <xsl:when test="(name(/*) = &quot;Article&quot;) and ($mml = &quot;0&quot;)">
                <xsl:text>1</xsl:text>
              </xsl:when>
              <xsl:otherwise>
                <xsl:text>0</xsl:text>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:variable>
          <xsl:call-template name="absref">
            <xsl:with-param name="elems" select="key($k1,$nr)[$pid=@relnr]"/>
            <xsl:with-param name="c" select="$c1"/>
            <xsl:with-param name="sym" select="$sym"/>
            <xsl:with-param name="pid" select="$pid"/>
          </xsl:call-template>
        </xsl:for-each>
      </xsl:when>
      <xsl:otherwise>
        <xsl:variable name="doc">
          <xsl:choose>
            <xsl:when test="key($k,$nr)">
              <xsl:text/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:value-of select="$constrs"/>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:for-each select="document($doc,/)">
          <xsl:variable name="c1">
            <xsl:choose>
              <xsl:when test="(name(/*) = &quot;Article&quot;) and ($mml = &quot;0&quot;)">
                <xsl:text>1</xsl:text>
              </xsl:when>
              <xsl:otherwise>
                <xsl:text>0</xsl:text>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:variable>
          <xsl:call-template name="absref">
            <xsl:with-param name="elems" select="key($k,$nr)"/>
            <xsl:with-param name="c" select="$c1"/>
            <xsl:with-param name="sym" select="$sym"/>
          </xsl:call-template>
        </xsl:for-each>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- pretty printer - gets arguments, visibility info from pattern, -->
  <!-- format telling arities, the linked symbol and optionally right bracket -->
  <!-- parenth hints to put the whole expression in parentheses, but this -->
  <!-- is overrriden if the expression uses functor brackets -->
  <!-- #loci tells to print loci instead of arguments -->
  <!-- #i is the bound var nbr -->
  <xsl:template name="pp">
    <xsl:param name="k"/>
    <xsl:param name="nr"/>
    <xsl:param name="args"/>
    <xsl:param name="parenth"/>
    <xsl:param name="pid"/>
    <xsl:param name="loci"/>
    <xsl:param name="i"/>
    <xsl:variable name="pkey" select="concat(&apos;P_&apos;,$k)"/>
    <!-- pattern number given -->
    <xsl:choose>
      <xsl:when test="$pid&gt;0">
        <xsl:variable name="doc">
          <xsl:choose>
            <xsl:when test="key($pkey,$nr)[$pid=@relnr]">
              <xsl:text/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:value-of select="$patts"/>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:for-each select="document($doc,/)">
          <xsl:choose>
            <xsl:when test="key($pkey,$nr)[$pid=@relnr]">
              <xsl:for-each select="key($pkey,$nr)[$pid=@relnr]">
                <xsl:variable name="npid">
                  <xsl:if test="@redefnr&gt;0">
                    <xsl:value-of select="$pid"/>
                  </xsl:if>
                </xsl:variable>
                <xsl:call-template name="pp1">
                  <xsl:with-param name="k" select="$k"/>
                  <xsl:with-param name="nr" select="$nr"/>
                  <xsl:with-param name="args" select="$args"/>
                  <xsl:with-param name="vis" select="Visible/Int"/>
                  <xsl:with-param name="fnr" select="@formatnr"/>
                  <xsl:with-param name="parenth" select="$parenth"/>
                  <xsl:with-param name="loci" select="$loci"/>
                  <xsl:with-param name="pid" select="$npid"/>
                  <xsl:with-param name="i" select="$i"/>
                </xsl:call-template>
              </xsl:for-each>
            </xsl:when>
            <!-- failure, print in absolute notation -->
            <xsl:otherwise>
              <xsl:call-template name="abs">
                <xsl:with-param name="k" select="$k"/>
                <xsl:with-param name="nr" select="$nr"/>
              </xsl:call-template>
              <xsl:text>(</xsl:text>
              <xsl:call-template name="list">
                <xsl:with-param name="separ">
                  <xsl:text>,</xsl:text>
                </xsl:with-param>
                <xsl:with-param name="elems" select="$args"/>
              </xsl:call-template>
              <xsl:text>)</xsl:text>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:for-each>
      </xsl:when>
      <!-- pattern number not given - take first suitable -->
      <xsl:otherwise>
        <xsl:variable name="doc">
          <xsl:choose>
            <xsl:when test="key($pkey,$nr)">
              <xsl:text/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:value-of select="$patts"/>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:for-each select="document($doc,/)">
          <xsl:choose>
            <xsl:when test="key($pkey,$nr)">
              <xsl:for-each select="key($pkey,$nr)[position()=1]">
                <xsl:variable name="npid">
                  <xsl:if test="@redefnr&gt;0">
                    <xsl:value-of select="@relnr"/>
                  </xsl:if>
                </xsl:variable>
                <xsl:call-template name="pp1">
                  <xsl:with-param name="k" select="$k"/>
                  <xsl:with-param name="nr" select="$nr"/>
                  <xsl:with-param name="args" select="$args"/>
                  <xsl:with-param name="vis" select="Visible/Int"/>
                  <xsl:with-param name="fnr" select="@formatnr"/>
                  <xsl:with-param name="parenth" select="$parenth"/>
                  <xsl:with-param name="loci" select="$loci"/>
                  <xsl:with-param name="pid" select="$npid"/>
                  <xsl:with-param name="i" select="$i"/>
                </xsl:call-template>
              </xsl:for-each>
            </xsl:when>
            <!-- failure, print in absolute notation -->
            <xsl:otherwise>
              <xsl:call-template name="abs">
                <xsl:with-param name="k" select="$k"/>
                <xsl:with-param name="nr" select="$nr"/>
              </xsl:call-template>
              <xsl:text>(</xsl:text>
              <xsl:call-template name="list">
                <xsl:with-param name="separ">
                  <xsl:text>,</xsl:text>
                </xsl:with-param>
                <xsl:with-param name="elems" select="$args"/>
              </xsl:call-template>
              <xsl:text>)</xsl:text>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:for-each>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- it is legal to pass only #loci instead of #args here -->
  <!-- #pid is passed to abs, causes linking to patterns -->
  <!-- #i is the bound var nbr -->
  <xsl:template name="pp1">
    <xsl:param name="k"/>
    <xsl:param name="nr"/>
    <xsl:param name="args"/>
    <xsl:param name="vis"/>
    <xsl:param name="fnr"/>
    <xsl:param name="parenth"/>
    <xsl:param name="loci"/>
    <xsl:param name="pid"/>
    <xsl:param name="i"/>
    <xsl:variable name="la">
      <xsl:choose>
        <xsl:when test="($k=&apos;M&apos;) or ($k=&apos;G&apos;) or ($k=&apos;L&apos;)">
          <xsl:text>0</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:for-each select="document($formats,/)">
            <xsl:for-each select="key(&apos;F&apos;,$fnr)">
              <xsl:choose>
                <xsl:when test="@leftargnr">
                  <xsl:value-of select="@leftargnr"/>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:text>0</xsl:text>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:for-each>
          </xsl:for-each>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <!-- try if right bracket - returns '' if not -->
    <xsl:variable name="rsym">
      <xsl:if test="($k=&apos;K&apos;) and ($la=&apos;0&apos;)">
        <xsl:call-template name="abs1">
          <xsl:with-param name="k" select="$k"/>
          <xsl:with-param name="nr" select="$nr"/>
          <xsl:with-param name="fnr" select="$fnr"/>
          <xsl:with-param name="r">
            <xsl:text>1</xsl:text>
          </xsl:with-param>
        </xsl:call-template>
      </xsl:if>
    </xsl:variable>
    <xsl:variable name="np">
      <xsl:choose>
        <xsl:when test="not($vis) or ($k=&apos;G&apos;)">
          <xsl:text>0</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:choose>
            <xsl:when test="$parenth&gt;0">
              <xsl:value-of select="$parenth"/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:choose>
                <xsl:when test="not($rsym=&apos;&apos;)">
                  <xsl:text>1</xsl:text>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:text>0</xsl:text>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="paren_color" select="$np mod $pcolors_nr"/>
    <!-- print spanned paranthesis or left bracket -->
    <xsl:choose>
      <xsl:when test="($parenspans = 1) and ($np &gt; 0)">
        <xsl:element name="span">
          <xsl:attribute name="class">
            <xsl:value-of select="concat(&quot;p&quot;,$paren_color)"/>
          </xsl:attribute>
          <xsl:choose>
            <xsl:when test="$rsym=&apos;&apos;">
              <xsl:text>(</xsl:text>
            </xsl:when>
            <xsl:otherwise>
              <xsl:call-template name="abs">
                <xsl:with-param name="k" select="$k"/>
                <xsl:with-param name="nr" select="$nr"/>
                <xsl:with-param name="sym">
                  <xsl:call-template name="abs1">
                    <xsl:with-param name="k" select="$k"/>
                    <xsl:with-param name="nr" select="$nr"/>
                    <xsl:with-param name="fnr" select="$fnr"/>
                  </xsl:call-template>
                </xsl:with-param>
                <xsl:with-param name="pid" select="$pid"/>
              </xsl:call-template>
            </xsl:otherwise>
          </xsl:choose>
          <xsl:element name="span">
            <xsl:attribute name="class">
              <xsl:text>default</xsl:text>
            </xsl:attribute>
            <xsl:call-template name="pp2">
              <xsl:with-param name="k" select="$k"/>
              <xsl:with-param name="nr" select="$nr"/>
              <xsl:with-param name="i" select="$i"/>
              <xsl:with-param name="vis" select="$vis"/>
              <xsl:with-param name="la" select="$la"/>
              <xsl:with-param name="loci" select="$loci"/>
              <xsl:with-param name="args" select="$args"/>
              <xsl:with-param name="np" select="$np"/>
              <xsl:with-param name="rsym" select="$rsym"/>
              <xsl:with-param name="parenth" select="$parenth"/>
              <xsl:with-param name="fnr" select="$fnr"/>
              <xsl:with-param name="pid" select="$pid"/>
            </xsl:call-template>
          </xsl:element>
          <xsl:choose>
            <xsl:when test="$rsym=&apos;&apos;">
              <xsl:text>)</xsl:text>
            </xsl:when>
            <xsl:otherwise>
              <xsl:call-template name="abs">
                <xsl:with-param name="k" select="$k"/>
                <xsl:with-param name="nr" select="$nr"/>
                <xsl:with-param name="sym" select="$rsym"/>
                <xsl:with-param name="pid" select="$pid"/>
              </xsl:call-template>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:if test="($np &gt; 0)">
          <xsl:choose>
            <xsl:when test="$rsym=&apos;&apos;">
              <xsl:text>(</xsl:text>
            </xsl:when>
            <xsl:otherwise>
              <xsl:call-template name="abs">
                <xsl:with-param name="k" select="$k"/>
                <xsl:with-param name="nr" select="$nr"/>
                <xsl:with-param name="sym">
                  <xsl:call-template name="abs1">
                    <xsl:with-param name="k" select="$k"/>
                    <xsl:with-param name="nr" select="$nr"/>
                    <xsl:with-param name="fnr" select="$fnr"/>
                  </xsl:call-template>
                </xsl:with-param>
                <xsl:with-param name="pid" select="$pid"/>
              </xsl:call-template>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:if>
        <xsl:call-template name="pp2">
          <xsl:with-param name="k" select="$k"/>
          <xsl:with-param name="nr" select="$nr"/>
          <xsl:with-param name="i" select="$i"/>
          <xsl:with-param name="vis" select="$vis"/>
          <xsl:with-param name="la" select="$la"/>
          <xsl:with-param name="loci" select="$loci"/>
          <xsl:with-param name="args" select="$args"/>
          <xsl:with-param name="np" select="$np"/>
          <xsl:with-param name="rsym" select="$rsym"/>
          <xsl:with-param name="parenth" select="$parenth"/>
          <xsl:with-param name="fnr" select="$fnr"/>
          <xsl:with-param name="pid" select="$pid"/>
        </xsl:call-template>
        <xsl:if test="($np &gt; 0)">
          <xsl:choose>
            <xsl:when test="$rsym=&apos;&apos;">
              <xsl:text>)</xsl:text>
            </xsl:when>
            <xsl:otherwise>
              <xsl:call-template name="abs">
                <xsl:with-param name="k" select="$k"/>
                <xsl:with-param name="nr" select="$nr"/>
                <xsl:with-param name="sym" select="$rsym"/>
                <xsl:with-param name="pid" select="$pid"/>
              </xsl:call-template>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:if>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="pp2">
    <xsl:param name="k"/>
    <xsl:param name="nr"/>
    <xsl:param name="i"/>
    <xsl:param name="vis"/>
    <xsl:param name="la"/>
    <xsl:param name="loci"/>
    <xsl:param name="args"/>
    <xsl:param name="np"/>
    <xsl:param name="rsym"/>
    <xsl:param name="parenth"/>
    <xsl:param name="fnr"/>
    <xsl:param name="pid"/>
    <!-- print left args -->
    <xsl:for-each select="$vis">
      <xsl:if test="position() &lt;= $la">
        <xsl:variable name="x" select="@x"/>
        <xsl:choose>
          <xsl:when test="$loci&gt;0">
            <xsl:choose>
              <xsl:when test="$loci=&quot;2&quot;">
                <xsl:call-template name="ppconst">
                  <xsl:with-param name="nr" select="$x"/>
                  <xsl:with-param name="vid" select="$args[position()=$x]/@vid"/>
                </xsl:call-template>
              </xsl:when>
              <xsl:otherwise>
                <xsl:call-template name="ploci">
                  <xsl:with-param name="nr" select="$x"/>
                </xsl:call-template>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:when>
          <xsl:otherwise>
            <xsl:apply-templates select="$args[position() = $x]">
              <xsl:with-param name="p" select="$np"/>
              <xsl:with-param name="i" select="$i"/>
            </xsl:apply-templates>
          </xsl:otherwise>
        </xsl:choose>
        <xsl:if test="position() &lt; $la">
          <xsl:text>,</xsl:text>
        </xsl:if>
      </xsl:if>
    </xsl:for-each>
    <!-- print symbol -->
    <xsl:if test="$rsym=&apos;&apos;">
      <xsl:if test="not($parenth&gt;0) or ($la&gt;0)">
        <xsl:text> </xsl:text>
      </xsl:if>
      <xsl:call-template name="abs">
        <xsl:with-param name="k" select="$k"/>
        <xsl:with-param name="nr" select="$nr"/>
        <xsl:with-param name="sym">
          <xsl:call-template name="abs1">
            <xsl:with-param name="k" select="$k"/>
            <xsl:with-param name="nr" select="$nr"/>
            <xsl:with-param name="fnr" select="$fnr"/>
          </xsl:call-template>
        </xsl:with-param>
        <xsl:with-param name="pid" select="$pid"/>
      </xsl:call-template>
      <xsl:if test="$k=&apos;G&apos;">
        <xsl:text>(#</xsl:text>
      </xsl:if>
      <xsl:text> </xsl:text>
    </xsl:if>
    <!-- print right args preceded by "of" for types -->
    <xsl:for-each select="$vis">
      <xsl:if test="(position() = 1) and (($k=&apos;M&apos;) or ($k=&apos;L&apos;))">
        <xsl:text>of </xsl:text>
      </xsl:if>
      <xsl:if test="position() &gt; $la">
        <xsl:variable name="x" select="@x"/>
        <xsl:choose>
          <xsl:when test="$loci&gt;0">
            <xsl:choose>
              <xsl:when test="$loci=&quot;2&quot;">
                <xsl:call-template name="ppconst">
                  <xsl:with-param name="nr" select="$x"/>
                  <xsl:with-param name="vid" select="$args[position()=$x]/@vid"/>
                </xsl:call-template>
              </xsl:when>
              <xsl:otherwise>
                <xsl:call-template name="ploci">
                  <xsl:with-param name="nr" select="$x"/>
                </xsl:call-template>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:when>
          <xsl:otherwise>
            <xsl:apply-templates select="$args[position()  = $x]">
              <xsl:with-param name="p" select="$np"/>
              <xsl:with-param name="i" select="$i"/>
            </xsl:apply-templates>
          </xsl:otherwise>
        </xsl:choose>
        <xsl:if test="position() &lt; last()">
          <xsl:text>,</xsl:text>
        </xsl:if>
      </xsl:if>
    </xsl:for-each>
    <xsl:if test="$k=&apos;G&apos;">
      <xsl:text> #)</xsl:text>
    </xsl:if>
  </xsl:template>

  <!-- theorem, definition and scheme references -->
  <xsl:template name="getref">
    <xsl:param name="k"/>
    <xsl:param name="anr"/>
    <xsl:param name="nr"/>
    <xsl:choose>
      <xsl:when test="$anr&gt;0">
        <xsl:variable name="refdoc">
          <xsl:choose>
            <xsl:when test="$k=&quot;S&quot;">
              <xsl:value-of select="$schms"/>
            </xsl:when>
            <xsl:otherwise>
              <xsl:value-of select="$thms"/>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:for-each select="document($refdoc,/)">
          <xsl:for-each select="key($k,concat($anr,&apos;:&apos;,$nr))[position()=1]">
            <xsl:call-template name="mkref">
              <xsl:with-param name="aid" select="@aid"/>
              <xsl:with-param name="nr" select="$nr"/>
              <xsl:with-param name="k" select="$k"/>
            </xsl:call-template>
          </xsl:for-each>
        </xsl:for-each>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="mkref">
          <xsl:with-param name="aid" select="$aname"/>
          <xsl:with-param name="nr" select="$nr"/>
          <xsl:with-param name="k" select="$k"/>
          <xsl:with-param name="c">
            <xsl:text>1</xsl:text>
          </xsl:with-param>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- find the constant with #nr on level #pl or higher, -->
  <!-- and pretty print it -->
  <!-- now assumes that proof levels are available, which is only through -->
  <!-- addabsrefs preprocessing -->
  <xsl:template name="absconst">
    <xsl:param name="nr"/>
    <xsl:param name="pl"/>
    <xsl:choose>
      <xsl:when test="key(&quot;C&quot;,$pl)[@nr = $nr]">
        <xsl:for-each select="key(&quot;C&quot;,$pl)[@nr = $nr]">
          <xsl:call-template name="ppconst">
            <xsl:with-param name="nr" select="$nr"/>
            <xsl:with-param name="vid" select="Typ[position() = 1]/@vid"/>
          </xsl:call-template>
        </xsl:for-each>
      </xsl:when>
      <xsl:otherwise>
        <xsl:choose>
          <xsl:when test="key(&quot;C&quot;,$pl)[@nr &lt; $nr]">
            <xsl:for-each select="key(&quot;C&quot;,$pl)[@nr &lt; $nr]">
              <xsl:if test="position() = last()">
                <xsl:variable name="n1">
                  <xsl:call-template name="getcnr">
                    <xsl:with-param name="el" select="."/>
                  </xsl:call-template>
                </xsl:variable>
                <xsl:variable name="lastnr" select="@nr + $n1 - 1"/>
                <xsl:variable name="n2" select="@nr"/>
                <xsl:choose>
                  <xsl:when test="$lastnr &gt;= $nr">
                    <xsl:call-template name="ppconst">
                      <xsl:with-param name="nr" select="$nr"/>
                      <xsl:with-param name="vid" select="Typ[position() = ($nr - $n2 + 1)]/@vid"/>
                    </xsl:call-template>
                  </xsl:when>
                  <xsl:otherwise>
                    <xsl:value-of select="$dbgmsg"/>
                  </xsl:otherwise>
                </xsl:choose>
              </xsl:if>
            </xsl:for-each>
          </xsl:when>
          <xsl:otherwise>
            <xsl:variable name="ls" select="string-length($pl)"/>
            <xsl:choose>
              <xsl:when test="$ls&gt;0">
                <xsl:variable name="pl1">
                  <xsl:call-template name="get_parent_level">
                    <xsl:with-param name="pl" select="$pl"/>
                    <xsl:with-param name="ls" select="$ls"/>
                    <xsl:with-param name="n">
                      <xsl:text>1</xsl:text>
                    </xsl:with-param>
                  </xsl:call-template>
                </xsl:variable>
                <xsl:call-template name="absconst">
                  <xsl:with-param name="nr" select="$nr"/>
                  <xsl:with-param name="pl" select="$pl1"/>
                </xsl:call-template>
              </xsl:when>
              <xsl:otherwise>
                <xsl:value-of select="$dbgmsg"/>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!--  -->
  <!-- File: reasoning.xsltxt - html-ization of Mizar XML, code for reasoning items -->
  <!--  -->
  <!-- Author: Josef Urban -->
  <!--  -->
  <!-- License: GPL (GNU GENERAL PUBLIC LICENSE) -->
  <xsl:template match="Proposition">
    <xsl:if test="$proof_links&gt;0">
      <xsl:element name="a">
        <xsl:attribute name="NAME">
          <xsl:call-template name="propname">
            <xsl:with-param name="n" select="@propnr"/>
            <xsl:with-param name="pl" select="@plevel"/>
          </xsl:call-template>
        </xsl:attribute>
      </xsl:element>
    </xsl:if>
    <xsl:if test="following-sibling::*[1][(name()=&quot;By&quot;) and (@linked=&quot;true&quot;)]">
      <xsl:if test="not((name(..) = &quot;Consider&quot;) or (name(..) = &quot;Reconsider&quot;) 
           or (name(..) = &quot;Conclusion&quot;))">
        <xsl:element name="b">
          <xsl:text>then </xsl:text>
        </xsl:element>
      </xsl:if>
    </xsl:if>
    <xsl:if test="@nr&gt;0">
      <xsl:choose>
        <xsl:when test="($proof_links&gt;0) and ($print_lab_identifiers = 0) 
            and not(string-length(@plevel)&gt;0)">
          <xsl:call-template name="plab1">
            <xsl:with-param name="nr" select="@nr"/>
            <xsl:with-param name="txt">
              <xsl:text>Lemma</xsl:text>
            </xsl:with-param>
          </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
          <xsl:call-template name="pplab">
            <xsl:with-param name="nr" select="@nr"/>
            <xsl:with-param name="vid" select="@vid"/>
          </xsl:call-template>
        </xsl:otherwise>
      </xsl:choose>
      <xsl:text>: </xsl:text>
    </xsl:if>
    <!-- ###TODO: include the possible link when generating items -->
    <xsl:choose>
      <xsl:when test="($generate_items&gt;0) and not(string-length(@plevel)&gt;0)">
        <xsl:choose>
          <xsl:when test="name(..) = &quot;SchemeBlock&quot;">
            <xsl:apply-templates/>
            <xsl:text> </xsl:text>
          </xsl:when>
          <xsl:otherwise>
            <xsl:if test="not(name(..) = &quot;SchemePremises&quot;)">
              <xsl:call-template name="pcomment">
                <xsl:with-param name="str" select="concat($aname, &quot;:lemma &quot;, @propnr)"/>
              </xsl:call-template>
            </xsl:if>
            <xsl:apply-templates/>
            <xsl:text> </xsl:text>
            <xsl:if test="($generate_items_proofs&gt;0) and
	      (following-sibling::*[1][(name()=&quot;By&quot;) or (name()=&quot;From&quot;) or (name()=&quot;Proof&quot;)])">
              <xsl:apply-templates select="following-sibling::*[1]"/>
            </xsl:if>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates/>
        <xsl:text> </xsl:text>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="mk_by_title">
    <xsl:param name="line"/>
    <xsl:param name="col"/>
    <xsl:value-of select="concat(&quot;Explain line &quot;, $line, &quot; column &quot;, $col)"/>
  </xsl:template>

  <!-- Justifications -->
  <xsl:template name="linkbyif">
    <xsl:param name="line"/>
    <xsl:param name="col"/>
    <xsl:param name="by"/>
    <xsl:choose>
      <xsl:when test="$linkby&gt;0">
        <xsl:variable name="byurl">
          <xsl:choose>
            <xsl:when test="$linkby=1">
              <xsl:value-of select="concat($lbydir,$anamelc,&quot;/&quot;,$line,&quot;_&quot;,$col,&quot;.html&quot;)"/>
            </xsl:when>
            <xsl:when test="$linkby=2">
              <xsl:value-of select="concat($lbydlicgipref,$anamelc,&quot;/&quot;,$line,&quot;_&quot;,$col,&quot;.dli&quot;)"/>
            </xsl:when>
            <xsl:when test="$linkby=3">
              <xsl:value-of select="concat($lbytptpcgi,&quot;?article=&quot;,$anamelc,&quot;&amp;lc=&quot;,$line,&quot;_&quot;,$col,&quot;&amp;tmp=&quot;,$lbytmpdir)"/>
            </xsl:when>
          </xsl:choose>
        </xsl:variable>
        <xsl:element name="a">
          <xsl:choose>
            <xsl:when test="$ajax_by &gt; 0">
              <xsl:call-template name="add_ajax_attrs">
                <xsl:with-param name="u" select="$byurl"/>
              </xsl:call-template>
            </xsl:when>
            <xsl:otherwise>
              <xsl:attribute name="href">
                <xsl:value-of select="$byurl"/>
              </xsl:attribute>
              <xsl:attribute name="class">
                <xsl:text>txt</xsl:text>
              </xsl:attribute>
              <xsl:choose>
                <xsl:when test="$linkbytoself &gt; 0">
                  <xsl:attribute name="target">
                    <xsl:text>_self</xsl:text>
                  </xsl:attribute>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:attribute name="target">
                    <xsl:text>byATP</xsl:text>
                  </xsl:attribute>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:otherwise>
          </xsl:choose>
          <xsl:if test="$by_titles&gt;0">
            <xsl:attribute name="title">
              <xsl:call-template name="mk_by_title">
                <xsl:with-param name="line" select="$line"/>
                <xsl:with-param name="col" select="$col"/>
              </xsl:call-template>
            </xsl:attribute>
          </xsl:if>
          <xsl:element name="b">
            <xsl:value-of select="$by"/>
            <xsl:text> </xsl:text>
          </xsl:element>
        </xsl:element>
        <xsl:if test="$ajax_by &gt; 0">
          <xsl:element name="span">
            <xsl:text> </xsl:text>
          </xsl:element>
        </xsl:if>
      </xsl:when>
      <xsl:otherwise>
        <xsl:element name="b">
          <xsl:value-of select="$by"/>
          <xsl:text> </xsl:text>
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- if #nbr=1 then no <br; is put in the end -->
  <!-- (used e.g. for conclusions, where definitional -->
  <!-- expansions are handled on the same line) -->
  <xsl:template match="By	">
    <xsl:param name="nbr"/>
    <xsl:choose>
      <xsl:when test="(count(Ref)&gt;0)">
        <xsl:call-template name="linkbyif">
          <xsl:with-param name="line" select="@line"/>
          <xsl:with-param name="col" select="@col"/>
          <xsl:with-param name="by">
            <xsl:text>by</xsl:text>
          </xsl:with-param>
        </xsl:call-template>
        <xsl:element name="i">
          <xsl:call-template name="list">
            <xsl:with-param name="separ">
              <xsl:text>, </xsl:text>
            </xsl:with-param>
            <xsl:with-param name="elems" select="Ref"/>
          </xsl:call-template>
        </xsl:element>
        <xsl:text>;</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:choose>
          <xsl:when test="$linkby&gt;0">
            <xsl:call-template name="linkbyif">
              <xsl:with-param name="line" select="@line"/>
              <xsl:with-param name="col" select="@col"/>
              <xsl:with-param name="by">
                <xsl:text>;</xsl:text>
              </xsl:with-param>
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <xsl:text>;</xsl:text>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
    <xsl:if test="not($nbr = &quot;1&quot;)">
      <xsl:element name="br"/>
    </xsl:if>
  </xsl:template>

  <xsl:template match="IterStep/By">
    <xsl:if test="(count(Ref)&gt;0)">
      <xsl:call-template name="linkbyif">
        <xsl:with-param name="line" select="@line"/>
        <xsl:with-param name="col" select="@col"/>
        <xsl:with-param name="by">
          <xsl:text>by</xsl:text>
        </xsl:with-param>
      </xsl:call-template>
      <xsl:element name="i">
        <xsl:call-template name="list">
          <xsl:with-param name="separ">
            <xsl:text>, </xsl:text>
          </xsl:with-param>
          <xsl:with-param name="elems" select="Ref"/>
        </xsl:call-template>
      </xsl:element>
    </xsl:if>
  </xsl:template>

  <xsl:template match="From">
    <xsl:param name="nbr"/>
    <xsl:call-template name="linkbyif">
      <xsl:with-param name="line" select="@line"/>
      <xsl:with-param name="col" select="@col"/>
      <xsl:with-param name="by">
        <xsl:text>from</xsl:text>
      </xsl:with-param>
    </xsl:call-template>
    <xsl:element name="i">
      <xsl:call-template name="getref">
        <xsl:with-param name="k">
          <xsl:text>S</xsl:text>
        </xsl:with-param>
        <xsl:with-param name="anr" select="@articlenr"/>
        <xsl:with-param name="nr" select="@nr"/>
      </xsl:call-template>
      <xsl:text>(</xsl:text>
      <xsl:call-template name="list">
        <xsl:with-param name="separ">
          <xsl:text>, </xsl:text>
        </xsl:with-param>
        <xsl:with-param name="elems" select="Ref"/>
      </xsl:call-template>
      <xsl:text>)</xsl:text>
      <xsl:text>;</xsl:text>
      <xsl:if test="not($nbr=&quot;1&quot;)">
        <xsl:element name="br"/>
      </xsl:if>
    </xsl:element>
  </xsl:template>

  <xsl:template match="IterStep/From">
    <xsl:call-template name="linkbyif">
      <xsl:with-param name="line" select="@line"/>
      <xsl:with-param name="col" select="@col"/>
      <xsl:with-param name="by">
        <xsl:text>from</xsl:text>
      </xsl:with-param>
    </xsl:call-template>
    <xsl:element name="i">
      <xsl:call-template name="getref">
        <xsl:with-param name="k">
          <xsl:text>S</xsl:text>
        </xsl:with-param>
        <xsl:with-param name="anr" select="@articlenr"/>
        <xsl:with-param name="nr" select="@nr"/>
      </xsl:call-template>
      <xsl:text>(</xsl:text>
      <xsl:call-template name="list">
        <xsl:with-param name="separ">
          <xsl:text>, </xsl:text>
        </xsl:with-param>
        <xsl:with-param name="elems" select="Ref"/>
      </xsl:call-template>
      <xsl:text>)</xsl:text>
    </xsl:element>
  </xsl:template>

  <!-- ##REQUIRE: the following two can be called only if $proof_links>0 -->
  <xsl:template name="top_propname">
    <xsl:param name="el"/>
    <xsl:for-each select="$el/..">
      <xsl:choose>
        <xsl:when test="(name() = &quot;DefTheorem&quot;) or (name() = &quot;JustifiedTheorem&quot;)">
          <xsl:variable name="k">
            <xsl:choose>
              <xsl:when test="@kind=&apos;D&apos;">
                <xsl:text>Def</xsl:text>
              </xsl:when>
              <xsl:otherwise>
                <xsl:text>Th</xsl:text>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:variable>
          <xsl:variable name="nm">
            <xsl:choose>
              <xsl:when test="($print_lab_identifiers &gt; 0) and ($el/@vid &gt; 0)">
                <xsl:call-template name="get_vid_name">
                  <xsl:with-param name="vid" select="$el/@vid"/>
                </xsl:call-template>
              </xsl:when>
              <xsl:otherwise>
                <xsl:value-of select="concat($k,@nr)"/>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:variable>
          <xsl:call-template name="mkref">
            <xsl:with-param name="aid" select="$aname"/>
            <xsl:with-param name="nr" select="@nr"/>
            <xsl:with-param name="k" select="@kind"/>
            <xsl:with-param name="c">
              <xsl:text>1</xsl:text>
            </xsl:with-param>
            <xsl:with-param name="nm" select="$nm"/>
          </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
          <xsl:variable name="k1" select="concat($el/@nr,&quot;:&quot;)"/>
          <xsl:variable name="k2" select="key(&quot;E&quot;,$k1)/@propnr"/>
          <xsl:element name="a">
            <xsl:attribute name="class">
              <xsl:text>txt</xsl:text>
            </xsl:attribute>
            <xsl:attribute name="href">
              <xsl:value-of select="concat($anamelc, &quot;.&quot;, $ext, &quot;#&quot;,&quot;E&quot;,$k2)"/>
            </xsl:attribute>
            <xsl:choose>
              <xsl:when test="($print_lab_identifiers &gt; 0) and ($el/@vid &gt; 0)">
                <xsl:call-template name="pplab">
                  <xsl:with-param name="nr" select="$el/@nr"/>
                  <xsl:with-param name="vid" select="$el/@vid"/>
                </xsl:call-template>
              </xsl:when>
              <xsl:otherwise>
                <xsl:call-template name="plab1">
                  <xsl:with-param name="nr" select="$el/@nr"/>
                  <xsl:with-param name="txt">
                    <xsl:text>Lemma</xsl:text>
                  </xsl:with-param>
                </xsl:call-template>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:element>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <!-- name of private reference - name of the proposition -->
  <xsl:template name="privname">
    <xsl:param name="nr"/>
    <xsl:param name="pl"/>
    <xsl:variable name="k1" select="concat($nr,&quot;:&quot;,$pl)"/>
    <xsl:choose>
      <xsl:when test="key(&quot;E&quot;,$k1)">
        <xsl:for-each select="key(&quot;E&quot;,$k1)">
          <xsl:choose>
            <xsl:when test="not(string-length($pl)&gt;0)">
              <xsl:call-template name="top_propname">
                <xsl:with-param name="el" select="."/>
              </xsl:call-template>
            </xsl:when>
            <xsl:otherwise>
              <xsl:variable name="txt">
                <xsl:call-template name="propname">
                  <xsl:with-param name="n" select="@propnr"/>
                  <xsl:with-param name="pl" select="$pl"/>
                </xsl:call-template>
              </xsl:variable>
              <xsl:element name="a">
                <xsl:attribute name="class">
                  <xsl:text>txt</xsl:text>
                </xsl:attribute>
                <!-- @href  = `concat($anamelc, ".", $ext, "#",$txt)`; -->
                <xsl:attribute name="href">
                  <xsl:value-of select="concat(&quot;#&quot;,$txt)"/>
                </xsl:attribute>
                <xsl:call-template name="pplab">
                  <xsl:with-param name="nr" select="@nr"/>
                  <xsl:with-param name="vid" select="@vid"/>
                </xsl:call-template>
              </xsl:element>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:for-each>
      </xsl:when>
      <xsl:otherwise>
        <xsl:variable name="ls" select="string-length($pl)"/>
        <xsl:if test="$ls&gt;0">
          <xsl:variable name="pl1">
            <xsl:call-template name="get_parent_level">
              <xsl:with-param name="pl" select="$pl"/>
              <xsl:with-param name="ls" select="$ls"/>
              <xsl:with-param name="n">
                <xsl:text>1</xsl:text>
              </xsl:with-param>
            </xsl:call-template>
          </xsl:variable>
          <xsl:call-template name="privname">
            <xsl:with-param name="nr" select="$nr"/>
            <xsl:with-param name="pl" select="$pl1"/>
          </xsl:call-template>
        </xsl:if>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- count local constants introduced in the current element - -->
  <!-- this asssumes Let | Given | TakeAsVar | Consider | Set | Reconsider -->
  <xsl:template name="getcnr">
    <xsl:param name="el"/>
    <xsl:value-of select="count($el/Typ)"/>
  </xsl:template>

  <!-- relies on addabsrefs preprocessing -->
  <xsl:template name="get_nearest_level">
    <xsl:param name="el"/>
    <xsl:for-each select="$el">
      <xsl:choose>
        <xsl:when test="@newlevel">
          <xsl:value-of select="@newlevel"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:call-template name="get_nearest_level">
            <xsl:with-param name="el" select=".."/>
          </xsl:call-template>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:for-each>
  </xsl:template>

  <xsl:template match="Ref">
    <xsl:choose>
      <xsl:when test="not(@articlenr)">
        <xsl:choose>
          <xsl:when test="$proof_links = 0">
            <!-- experimental!! -->
            <xsl:variable name="n1" select="@nr"/>
            <xsl:variable name="vid">
              <xsl:choose>
                <xsl:when test="@vid">
                  <xsl:value-of select="@vid"/>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:choose>
                    <xsl:when test="$print_lab_identifiers &gt; 0">
                      <!-- for-each [preceding::*[((name()="Proposition") or (name()="Now") or (name()="IterEquality")) and (@nr=$n1)][1]] -->
                      <!-- this seems to be reasonably fast -->
                      <xsl:for-each select="(preceding::Proposition[@nr=$n1]|preceding::Now[@nr=$n1]
                           |preceding::IterEquality[@nr=$n1])[last()]">
                        <xsl:value-of select="@vid"/>
                      </xsl:for-each>
                    </xsl:when>
                    <xsl:otherwise>
                      <xsl:text>0</xsl:text>
                    </xsl:otherwise>
                  </xsl:choose>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:variable>
            <xsl:call-template name="pplab">
              <xsl:with-param name="nr" select="$n1"/>
              <xsl:with-param name="vid" select="$vid"/>
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <xsl:variable name="pl">
              <xsl:call-template name="get_nearest_level">
                <xsl:with-param name="el" select=".."/>
              </xsl:call-template>
            </xsl:variable>
            <xsl:call-template name="privname">
              <xsl:with-param name="nr" select="@nr"/>
              <xsl:with-param name="pl" select="$pl"/>
            </xsl:call-template>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="getref">
          <xsl:with-param name="k" select="@kind"/>
          <xsl:with-param name="anr" select="@articlenr"/>
          <xsl:with-param name="nr" select="@nr"/>
        </xsl:call-template>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="ErrorInf">
    <xsl:param name="nbr"/>
    <xsl:text>errorinference;</xsl:text>
    <xsl:if test="not($nbr=&quot;1&quot;)">
      <xsl:element name="br"/>
    </xsl:if>
  </xsl:template>

  <xsl:template match="IterStep/ErrorInf">
    <xsl:text>errorinference</xsl:text>
  </xsl:template>

  <xsl:template match="SkippedProof">
    <xsl:param name="nbr"/>
    <xsl:element name="b">
      <xsl:text>@proof .. end;</xsl:text>
    </xsl:element>
    <xsl:if test="not($nbr=&quot;1&quot;)">
      <xsl:element name="br"/>
    </xsl:if>
  </xsl:template>

  <xsl:template match="IterStep/SkippedProof">
    <xsl:element name="b">
      <xsl:text>@proof .. end;</xsl:text>
    </xsl:element>
  </xsl:template>

  <!-- Term, elIterStep+ -->
  <xsl:template match="IterEquality">
    <xsl:param name="nbr"/>
    <xsl:if test="IterStep[1]/By[@linked=&quot;true&quot;]">
      <xsl:if test="not(name(..)=&quot;Conclusion&quot;)">
        <xsl:element name="b">
          <xsl:text>then </xsl:text>
        </xsl:element>
      </xsl:if>
    </xsl:if>
    <xsl:if test="@nr&gt;0">
      <xsl:call-template name="pplab">
        <xsl:with-param name="nr" select="@nr"/>
        <xsl:with-param name="vid" select="@vid"/>
      </xsl:call-template>
      <xsl:text>: </xsl:text>
    </xsl:if>
    <xsl:apply-templates select="*[1]"/>
    <xsl:text> = </xsl:text>
    <xsl:call-template name="nlist">
      <xsl:with-param name="separ">
        <xsl:text>.= </xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="IterStep"/>
    </xsl:call-template>
    <xsl:text>;</xsl:text>
    <xsl:if test="not($nbr=&quot;1&quot;)">
      <xsl:element name="br"/>
    </xsl:if>
  </xsl:template>

  <xsl:template match="IterStep">
    <xsl:apply-templates/>
  </xsl:template>

  <!-- Skeleton steps -->
  <!-- tpl [Let] { $j=`@nr`; <b { "let "; } pconst(#nr=$j); -->
  <!-- " be "; -->
  <!-- jlist(#j=$j, #sep2=" be ", #elems=`*`); -->
  <!-- ";"; try_th_exps(); <br; } -->
  <!-- #fst tells to process in a sequence of Let's -->
  <!-- #beg is the beginning of const. sequence numbers -->
  <xsl:template match="Let">
    <xsl:param name="fst"/>
    <xsl:param name="beg"/>
    <xsl:variable name="has_thesis">
      <xsl:choose>
        <xsl:when test="following-sibling::*[1][name()=&quot;Thesis&quot;]">
          <xsl:text>1</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="it_step">
      <xsl:choose>
        <xsl:when test="$has_thesis=&quot;1&quot;">
          <xsl:text>2</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>1</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:choose>
      <xsl:when test="not($fst=&quot;1&quot;) and (preceding-sibling::*[position()=$it_step][name()=&quot;Let&quot;])"/>
      <xsl:otherwise>
        <!-- try next Let for the same type - we cannot deal with thesis here -->
        <xsl:variable name="next">
          <xsl:choose>
            <xsl:when test="(count(Typ)=1) and 
         (following-sibling::*[position()=$it_step][name()=&quot;Let&quot;][count(Typ)=1]) and
	 (($has_thesis=&quot;0&quot;) or 
	  ((following-sibling::*[1][name()=&quot;Thesis&quot;][not(ThesisExpansions/Pair)])
	   and
	   (following-sibling::*[3][name()=&quot;Thesis&quot;][not(ThesisExpansions/Pair)])))">
              <xsl:call-template name="are_equal_vid">
                <xsl:with-param name="el1" select="./Typ"/>
                <xsl:with-param name="el2" select="following-sibling::*[position()=$it_step]/Typ"/>
              </xsl:call-template>
            </xsl:when>
            <xsl:otherwise>
              <xsl:text>0</xsl:text>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:choose>
          <xsl:when test="$beg">
            <xsl:text>, </xsl:text>
            <xsl:if test="$const_links&gt;0">
              <xsl:variable name="addpl">
                <xsl:call-template name="addp">
                  <xsl:with-param name="pl" select="@plevel"/>
                </xsl:call-template>
              </xsl:variable>
              <xsl:element name="a">
                <xsl:attribute name="NAME">
                  <xsl:value-of select="concat(&quot;c&quot;,@nr,$addpl)"/>
                </xsl:attribute>
              </xsl:element>
            </xsl:if>
            <xsl:call-template name="ppconst">
              <xsl:with-param name="nr" select="@nr"/>
              <xsl:with-param name="vid" select="Typ/@vid"/>
            </xsl:call-template>
            <xsl:choose>
              <xsl:when test="$next=&quot;1&quot;">
                <xsl:apply-templates select="following-sibling::*[position()=$it_step]">
                  <xsl:with-param name="fst">
                    <xsl:text>1</xsl:text>
                  </xsl:with-param>
                  <xsl:with-param name="beg" select="$beg"/>
                </xsl:apply-templates>
              </xsl:when>
              <xsl:otherwise>
                <xsl:text> be </xsl:text>
                <xsl:apply-templates select="Typ"/>
                <xsl:text>;</xsl:text>
                <xsl:call-template name="try_th_exps"/>
                <xsl:element name="br"/>
                <xsl:apply-templates select="following-sibling::*[position()=$it_step][name()=&quot;Let&quot;]">
                  <xsl:with-param name="fst">
                    <xsl:text>1</xsl:text>
                  </xsl:with-param>
                </xsl:apply-templates>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:when>
          <xsl:otherwise>
            <xsl:element name="b">
              <xsl:text>let </xsl:text>
            </xsl:element>
            <xsl:choose>
              <xsl:when test="$next=&quot;1&quot;">
                <xsl:if test="$const_links&gt;0">
                  <xsl:variable name="addpl">
                    <xsl:call-template name="addp">
                      <xsl:with-param name="pl" select="@plevel"/>
                    </xsl:call-template>
                  </xsl:variable>
                  <xsl:element name="a">
                    <xsl:attribute name="NAME">
                      <xsl:value-of select="concat(&quot;c&quot;,@nr,$addpl)"/>
                    </xsl:attribute>
                  </xsl:element>
                </xsl:if>
                <xsl:call-template name="ppconst">
                  <xsl:with-param name="nr" select="@nr"/>
                  <xsl:with-param name="vid" select="Typ/@vid"/>
                </xsl:call-template>
                <xsl:apply-templates select="following-sibling::*[position()=$it_step]">
                  <xsl:with-param name="fst">
                    <xsl:text>1</xsl:text>
                  </xsl:with-param>
                  <xsl:with-param name="beg" select="@nr"/>
                </xsl:apply-templates>
              </xsl:when>
              <xsl:otherwise>
                <xsl:call-template name="jtlist">
                  <xsl:with-param name="j" select="@nr - 1"/>
                  <xsl:with-param name="sep2">
                    <xsl:text> be </xsl:text>
                  </xsl:with-param>
                  <xsl:with-param name="elems" select="Typ"/>
                  <xsl:with-param name="pl" select="@plevel"/>
                </xsl:call-template>
                <xsl:text>;</xsl:text>
                <xsl:call-template name="try_th_exps"/>
                <xsl:element name="br"/>
                <xsl:apply-templates select="following-sibling::*[position()=$it_step][name()=&quot;Let&quot;]">
                  <xsl:with-param name="fst">
                    <xsl:text>1</xsl:text>
                  </xsl:with-param>
                </xsl:apply-templates>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="Assume">
    <xsl:element name="b">
      <xsl:text>assume </xsl:text>
    </xsl:element>
    <xsl:if test="count(*)&gt;1">
      <xsl:element name="b">
        <xsl:text>that </xsl:text>
      </xsl:element>
      <xsl:element name="br"/>
    </xsl:if>
    <xsl:call-template name="andlist">
      <xsl:with-param name="elems" select="*"/>
    </xsl:call-template>
    <xsl:text>;</xsl:text>
    <xsl:call-template name="try_th_exps"/>
    <xsl:element name="br"/>
  </xsl:template>

  <!-- should handle both the new version with the existential statement -->
  <!-- at the first position, and also the old version without it -->
  <xsl:template match="Given">
    <xsl:variable name="j" select="@nr - 1"/>
    <xsl:element name="b">
      <xsl:text>given </xsl:text>
    </xsl:element>
    <xsl:call-template name="jtlist">
      <xsl:with-param name="j" select="$j"/>
      <xsl:with-param name="sep2">
        <xsl:text> being </xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="Typ"/>
      <xsl:with-param name="pl" select="@plevel"/>
    </xsl:call-template>
    <xsl:element name="b">
      <xsl:text> such that </xsl:text>
    </xsl:element>
    <xsl:call-template name="andlist">
      <xsl:with-param name="elems" select="*[(name()=&quot;Proposition&quot;) and (position() &gt; 1)]"/>
    </xsl:call-template>
    <xsl:text>;</xsl:text>
    <xsl:call-template name="try_th_exps"/>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="Take">
    <xsl:element name="b">
      <xsl:text>take </xsl:text>
    </xsl:element>
    <xsl:apply-templates/>
    <xsl:text>;</xsl:text>
    <xsl:call-template name="try_th_exps"/>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="TakeAsVar">
    <xsl:element name="b">
      <xsl:text>take </xsl:text>
    </xsl:element>
    <xsl:if test="$const_links&gt;0">
      <xsl:variable name="addpl">
        <xsl:call-template name="addp">
          <xsl:with-param name="pl" select="@plevel"/>
        </xsl:call-template>
      </xsl:variable>
      <xsl:element name="a">
        <xsl:attribute name="NAME">
          <xsl:value-of select="concat(&quot;c&quot;,@nr,$addpl)"/>
        </xsl:attribute>
      </xsl:element>
    </xsl:if>
    <xsl:call-template name="ppconst">
      <xsl:with-param name="nr" select="@nr"/>
      <xsl:with-param name="vid" select="Typ[1]/@vid"/>
    </xsl:call-template>
    <xsl:text> = </xsl:text>
    <xsl:apply-templates select="*[2]"/>
    <xsl:text>;</xsl:text>
    <xsl:call-template name="try_th_exps"/>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="Conclusion">
    <xsl:choose>
      <xsl:when test="(By[@linked = &quot;true&quot;]) or 
       (IterEquality/IterStep[1]/By[@linked = &quot;true&quot;])">
        <xsl:element name="b">
          <xsl:text>hence </xsl:text>
        </xsl:element>
        <xsl:apply-templates select="*[not(name() = &quot;By&quot;)]"/>
        <xsl:apply-templates select="By">
          <xsl:with-param name="nbr">
            <xsl:text>1</xsl:text>
          </xsl:with-param>
        </xsl:apply-templates>
        <xsl:call-template name="try_th_exps"/>
        <xsl:element name="br"/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:choose>
          <xsl:when test="Now">
            <xsl:element name="div">
              <xsl:element name="b">
                <xsl:text>hereby </xsl:text>
              </xsl:element>
              <xsl:call-template name="try_th_exps"/>
              <xsl:apply-templates>
                <xsl:with-param name="nkw">
                  <xsl:text>1</xsl:text>
                </xsl:with-param>
              </xsl:apply-templates>
              <xsl:element name="b">
                <xsl:text>end;</xsl:text>
              </xsl:element>
            </xsl:element>
          </xsl:when>
          <xsl:otherwise>
            <xsl:element name="b">
              <xsl:text>thus </xsl:text>
            </xsl:element>
            <xsl:choose>
              <xsl:when test="Proof">
                <xsl:apply-templates select="Proposition"/>
                <xsl:call-template name="try_th_exps"/>
                <xsl:apply-templates select="Proof"/>
              </xsl:when>
              <xsl:otherwise>
                <xsl:apply-templates select="Proposition"/>
                <xsl:apply-templates select=" IterEquality|By|From|ErrorInf|SkippedProof">
                  <xsl:with-param name="nbr">
                    <xsl:text>1</xsl:text>
                  </xsl:with-param>
                </xsl:apply-templates>
                <xsl:call-template name="try_th_exps"/>
                <xsl:element name="br"/>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- Auxiliary items -->
  <!-- First comes the reconstructed existential statement -->
  <!-- and its justification, then the new local constants -->
  <!-- and zero or more propositions about them. -->
  <!-- For easier presentation, nr optionally contains the number -->
  <!-- of the first local constant created here. -->
  <!--  -->
  <!-- element Consider { -->
  <!-- attribute nr { xsd:integer }?, -->
  <!-- Proposition, Justification, -->
  <!-- Typ+, Proposition* -->
  <!-- } -->
  <xsl:template match="Consider">
    <xsl:variable name="j" select="@nr - 1"/>
    <xsl:element name="b">
      <xsl:if test="By[@linked=&quot;true&quot;]">
        <xsl:text>then </xsl:text>
      </xsl:if>
      <xsl:text>consider </xsl:text>
    </xsl:element>
    <xsl:call-template name="jtlist">
      <xsl:with-param name="j" select="$j"/>
      <xsl:with-param name="sep2">
        <xsl:text> being </xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="Typ"/>
      <xsl:with-param name="pl" select="@plevel"/>
    </xsl:call-template>
    <xsl:if test="count(Proposition) &gt; 1">
      <xsl:element name="b">
        <xsl:text> such that </xsl:text>
      </xsl:element>
      <xsl:element name="br"/>
      <xsl:call-template name="andlist">
        <xsl:with-param name="elems" select="Proposition[position() &gt; 1]"/>
      </xsl:call-template>
    </xsl:if>
    <xsl:apply-templates select="*[2]"/>
  </xsl:template>

  <!-- First comes the series of target types and reconsidered terms. -->
  <!-- For all these terms a new local variable with its target type -->
  <!-- is created, and its equality to the corresponding term is remembered. -->
  <!-- Finally the proposition about the typing is given and justified. -->
  <!-- For easier presentation, atNr optionally contains the number -->
  <!-- of the first local constant created here. -->
  <!-- Each type may optionally have presentational info about -->
  <!-- the variable (atVid) inside. -->
  <!-- element elReconsider { -->
  <!-- attribute atNr { xsd:integer }?, -->
  <!-- (elTyp, Term)+, -->
  <!-- elProposition, Justification -->
  <!-- } -->
  <xsl:template match="Reconsider">
    <xsl:variable name="j" select="@nr"/>
    <xsl:element name="b">
      <xsl:if test="By[@linked=&quot;true&quot;]">
        <xsl:text>then </xsl:text>
      </xsl:if>
      <xsl:text>reconsider </xsl:text>
    </xsl:element>
    <xsl:variable name="addpl">
      <xsl:if test="$const_links&gt;0">
        <xsl:call-template name="addp">
          <xsl:with-param name="pl" select="@plevel"/>
        </xsl:call-template>
      </xsl:if>
    </xsl:variable>
    <!-- should work both for old and new reconsider -->
    <xsl:for-each select="*[(not(name() = &quot;Typ&quot;)) and (position() &lt; (last() - 1))]">
      <xsl:variable name="p1" select="position()"/>
      <xsl:variable name="nr1" select="$j + $p1 - 1"/>
      <xsl:if test="$const_links&gt;0">
        <xsl:element name="a">
          <xsl:attribute name="NAME">
            <xsl:value-of select="concat(&quot;c&quot;,$nr1,$addpl)"/>
          </xsl:attribute>
        </xsl:element>
      </xsl:if>
      <xsl:call-template name="ppconst">
        <xsl:with-param name="nr" select="$nr1"/>
        <xsl:with-param name="vid" select="../Typ[$p1]/@vid"/>
      </xsl:call-template>
      <xsl:text> = </xsl:text>
      <xsl:apply-templates select="."/>
      <xsl:if test="not($p1=last())">
        <xsl:text>, </xsl:text>
      </xsl:if>
    </xsl:for-each>
    <!-- ppconst(#nr=$j, #vid = `Typ[1]/@vid`); " = "; -->
    <!-- jlist(#j=$j, #sep2=" = ", #elems=`*[(not(name() = "Typ")) -->
    <!-- and (position() < (last() - 1))]`); -->
    <xsl:text> as </xsl:text>
    <xsl:apply-templates select="*[1]"/>
    <xsl:text> </xsl:text>
    <xsl:apply-templates select="*[last()]"/>
  </xsl:template>

  <xsl:template match="Set">
    <xsl:element name="b">
      <xsl:text>set </xsl:text>
    </xsl:element>
    <xsl:if test="$const_links&gt;0">
      <xsl:variable name="addpl">
        <xsl:call-template name="addp">
          <xsl:with-param name="pl" select="@plevel"/>
        </xsl:call-template>
      </xsl:variable>
      <xsl:element name="a">
        <xsl:attribute name="NAME">
          <xsl:value-of select="concat(&quot;c&quot;,@nr,$addpl)"/>
        </xsl:attribute>
      </xsl:element>
    </xsl:if>
    <xsl:call-template name="ppconst">
      <xsl:with-param name="nr" select="@nr"/>
      <xsl:with-param name="vid" select="Typ/@vid"/>
    </xsl:call-template>
    <xsl:text> = </xsl:text>
    <xsl:apply-templates select="*[1]"/>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="DefFunc">
    <xsl:element name="b">
      <xsl:text>deffunc </xsl:text>
    </xsl:element>
    <xsl:call-template name="ppfunc">
      <xsl:with-param name="nr" select="@nr"/>
    </xsl:call-template>
    <xsl:text>(</xsl:text>
    <xsl:call-template name="list">
      <xsl:with-param name="separ">
        <xsl:text>,</xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="ArgTypes/Typ"/>
    </xsl:call-template>
    <xsl:text>) </xsl:text>
    <xsl:element name="b">
      <xsl:text>-&gt; </xsl:text>
    </xsl:element>
    <xsl:apply-templates select="*[3]"/>
    <xsl:text> = </xsl:text>
    <xsl:apply-templates select="*[2]"/>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="DefPred">
    <xsl:element name="b">
      <xsl:text>defpred </xsl:text>
    </xsl:element>
    <xsl:call-template name="pppred">
      <xsl:with-param name="nr" select="@nr"/>
    </xsl:call-template>
    <xsl:text>[</xsl:text>
    <xsl:call-template name="list">
      <xsl:with-param name="separ">
        <xsl:text>,</xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="ArgTypes/Typ"/>
    </xsl:call-template>
    <xsl:text>] </xsl:text>
    <xsl:element name="b">
      <xsl:text>means </xsl:text>
    </xsl:element>
    <xsl:apply-templates select="*[2]"/>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <!-- Thesis after skeleton item, with definiens numbers -->
  <!-- forbid as default -->
  <xsl:template match="Thesis"/>

  <xsl:template name="do_thesis">
    <xsl:param name="nd"/>
    <xsl:apply-templates select="ThesisExpansions"/>
    <xsl:if test="($display_thesis = 1) and (not($nd = 1))">
      <xsl:text> </xsl:text>
      <xsl:element name="a">
        <xsl:call-template name="add_hs_attrs"/>
        <xsl:call-template name="pcomment0">
          <xsl:with-param name="str">
            <xsl:text> thesis: </xsl:text>
          </xsl:with-param>
        </xsl:call-template>
      </xsl:element>
      <xsl:element name="span">
        <xsl:attribute name="class">
          <xsl:text>hide</xsl:text>
        </xsl:attribute>
        <xsl:text> </xsl:text>
        <xsl:apply-templates select="*[1]"/>
      </xsl:element>
    </xsl:if>
  </xsl:template>

  <xsl:template name="try_th_exps_old">
    <xsl:apply-templates select="./following-sibling::*[1][name()=&quot;Thesis&quot;]/ThesisExpansions"/>
  </xsl:template>

  <!-- #nd overrides the $display_thesis parameter in do_thesis, -->
  <!-- used to supress the incorrect PerCases thesis now -->
  <xsl:template name="try_th_exps">
    <xsl:param name="nd"/>
    <xsl:choose>
      <xsl:when test="./following-sibling::*[1][name()=&quot;Thesis&quot;]">
        <xsl:for-each select="./following-sibling::*[1][name()=&quot;Thesis&quot;]">
          <xsl:call-template name="do_thesis">
            <xsl:with-param name="nd" select="$nd"/>
          </xsl:call-template>
        </xsl:for-each>
      </xsl:when>
      <xsl:otherwise>
        <xsl:if test="((name(..) = &quot;Now&quot;) or (name(..) = &quot;CaseBlock&quot;) or (name(..) = &quot;SupposeBlock&quot;))
              and (../BlockThesis/Thesis)">
          <xsl:variable name="prev_thesis_changes" select="count(./preceding-sibling::*[(name()=&quot;Let&quot;) or (name()=&quot;Take&quot;) 
	                               or (name()=&quot;TakeAsVar&quot;) or (name()=&quot;Assume&quot;)
	                               or (name()=&quot;Case&quot;) or (name()=&quot;Suppose&quot;)
				       or (name()=&quot;Given&quot;) or (name()=&quot;Conclusion&quot;)])"/>
          <xsl:for-each select=" ../BlockThesis/Thesis[$prev_thesis_changes + 1]">
            <xsl:call-template name="do_thesis">
              <xsl:with-param name="nd" select="$nd"/>
            </xsl:call-template>
          </xsl:for-each>
        </xsl:if>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template match="ThesisExpansions">
    <xsl:if test="Pair">
      <xsl:text> </xsl:text>
      <xsl:call-template name="pcomment0">
        <xsl:with-param name="str">
          <xsl:text>according to </xsl:text>
        </xsl:with-param>
      </xsl:call-template>
      <xsl:call-template name="list">
        <xsl:with-param name="separ">
          <xsl:text>,</xsl:text>
        </xsl:with-param>
        <xsl:with-param name="elems" select="Pair[@x]"/>
      </xsl:call-template>
    </xsl:if>
  </xsl:template>

  <xsl:template match="ThesisExpansions/Pair">
    <xsl:variable name="x" select="@x"/>
    <xsl:variable name="doc">
      <xsl:choose>
        <xsl:when test="key(&apos;DF&apos;,$x)">
          <xsl:text/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="$dfs"/>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="current">
      <xsl:choose>
        <xsl:when test="$doc=&quot;&quot;">
          <xsl:text>1</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>0</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:for-each select="document($doc,/)">
      <xsl:for-each select="key(&apos;DF&apos;,$x)">
        <xsl:call-template name="mkref">
          <xsl:with-param name="aid" select="@aid"/>
          <xsl:with-param name="nr" select="@defnr"/>
          <xsl:with-param name="k">
            <xsl:text>D</xsl:text>
          </xsl:with-param>
          <xsl:with-param name="c" select="$current"/>
        </xsl:call-template>
      </xsl:for-each>
    </xsl:for-each>
  </xsl:template>

  <!-- special block skeleton items -->
  <!-- element Suppose { Proposition+ } -->
  <!-- element Case { Proposition+ } -->
  <xsl:template match="Case|Suppose">
    <xsl:if test="count(*)&gt;1">
      <xsl:element name="b">
        <xsl:text>that </xsl:text>
      </xsl:element>
    </xsl:if>
    <xsl:call-template name="andlist">
      <xsl:with-param name="elems" select="*"/>
    </xsl:call-template>
    <xsl:text>;</xsl:text>
    <!-- this will break the thesis display in diffuse statements -->
    <!-- for earlier kernel (analyzer v. < 1.94) - mea culpa, -->
    <!-- the only reasonable backward-compatibility fix would be to -->
    <!-- keep the kernel version as a parameter and check it here -->
    <xsl:call-template name="try_th_exps"/>
    <xsl:element name="br"/>
  </xsl:template>

  <!-- element PerCases { Proposition, Inference } -->
  <xsl:template match="PerCases">
    <xsl:element name="a">
      <xsl:call-template name="add_hs_attrs"/>
      <xsl:element name="b">
        <xsl:text>cases </xsl:text>
      </xsl:element>
    </xsl:element>
    <xsl:element name="span">
      <xsl:attribute name="class">
        <xsl:text>hide</xsl:text>
      </xsl:attribute>
      <xsl:apply-templates select="*[1]"/>
    </xsl:element>
    <xsl:apply-templates select="*[position()&gt;1]"/>
    <!-- thesis after per cases is broken yet and would have -->
    <!-- to be reconstructed from subblocks' theses; -->
    <!-- don't display it, only display the expansions -->
    <xsl:call-template name="try_th_exps">
      <xsl:with-param name="nd">
        <xsl:text>1</xsl:text>
      </xsl:with-param>
    </xsl:call-template>
  </xsl:template>

  <!--  -->
  <!-- File: block_top.xsltxt - html-ization of Mizar XML, code for bloc and top elements -->
  <!--  -->
  <!-- Author: Josef Urban -->
  <!--  -->
  <!-- License: GPL (GNU GENERAL PUBLIC LICENSE) -->
  <!-- Registrations -->
  <xsl:template match="RCluster">
    <xsl:variable name="nr1" select="1 + count(preceding::RCluster)"/>
    <xsl:choose>
      <xsl:when test="$generate_items&gt;0">
        <xsl:document href="proofhtml/exreg/{$anamelc}.{$nr1}" format="html"> 
        <xsl:call-template name="rc"/>
        </xsl:document> 
        <xsl:variable name="bogus" select="1"/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="rc"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="rc">
    <xsl:if test="($mml=&quot;1&quot;) or ($generate_items&gt;0)">
      <xsl:apply-templates select="ArgTypes"/>
    </xsl:if>
    <xsl:variable name="nr1" select="1 + count(preceding::RCluster)"/>
    <xsl:element name="a">
      <xsl:attribute name="NAME">
        <xsl:value-of select="concat(&quot;RC&quot;,$nr1)"/>
      </xsl:attribute>
      <xsl:element name="b">
        <xsl:text>cluster </xsl:text>
      </xsl:element>
    </xsl:element>
    <xsl:choose>
      <xsl:when test="ErrorCluster">
        <xsl:text>errorcluster</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates select="*[3]"/>
        <xsl:text> </xsl:text>
        <xsl:apply-templates select="*[2]"/>
      </xsl:otherwise>
    </xsl:choose>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
    <xsl:if test="$mml=&quot;1&quot;">
      <xsl:element name="br"/>
    </xsl:if>
  </xsl:template>

  <xsl:template match="CCluster">
    <xsl:variable name="nr1" select="1 + count(preceding::CCluster)"/>
    <xsl:choose>
      <xsl:when test="$generate_items&gt;0">
        <xsl:document href="proofhtml/condreg/{$anamelc}.{$nr1}" format="html"> 
        <xsl:call-template name="cc"/>
        </xsl:document> 
        <xsl:variable name="bogus" select="1"/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="cc"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="cc">
    <xsl:if test="($mml=&quot;1&quot;) or ($generate_items&gt;0)">
      <xsl:apply-templates select="ArgTypes"/>
    </xsl:if>
    <xsl:variable name="nr1" select="1 + count(preceding::CCluster)"/>
    <xsl:element name="a">
      <xsl:attribute name="NAME">
        <xsl:value-of select="concat(&quot;CC&quot;,$nr1)"/>
      </xsl:attribute>
      <xsl:element name="b">
        <xsl:text>cluster </xsl:text>
      </xsl:element>
    </xsl:element>
    <xsl:choose>
      <xsl:when test="ErrorCluster">
        <xsl:text>errorcluster</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates select="*[2]"/>
        <xsl:element name="b">
          <xsl:text> -&gt; </xsl:text>
        </xsl:element>
        <xsl:apply-templates select="*[4]"/>
        <xsl:text> </xsl:text>
        <xsl:apply-templates select="*[3]"/>
      </xsl:otherwise>
    </xsl:choose>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
    <xsl:if test="$mml=&quot;1&quot;">
      <xsl:element name="br"/>
    </xsl:if>
  </xsl:template>

  <xsl:template match="FCluster">
    <xsl:variable name="nr1" select="1 + count(preceding::FCluster)"/>
    <xsl:choose>
      <xsl:when test="$generate_items&gt;0">
        <xsl:document href="proofhtml/funcreg/{$anamelc}.{$nr1}" format="html"> 
        <xsl:call-template name="fc"/>
        </xsl:document> 
        <xsl:variable name="bogus" select="1"/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="fc"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="fc">
    <xsl:if test="($mml=&quot;1&quot;) or ($generate_items&gt;0)">
      <xsl:apply-templates select="ArgTypes"/>
    </xsl:if>
    <xsl:variable name="nr1" select="1 + count(preceding::FCluster)"/>
    <xsl:element name="a">
      <xsl:attribute name="NAME">
        <xsl:value-of select="concat(&quot;FC&quot;,$nr1)"/>
      </xsl:attribute>
      <xsl:element name="b">
        <xsl:text>cluster </xsl:text>
      </xsl:element>
    </xsl:element>
    <xsl:choose>
      <xsl:when test="ErrorCluster">
        <xsl:text>errorcluster</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates select="*[2]"/>
        <xsl:element name="b">
          <xsl:text> -&gt; </xsl:text>
        </xsl:element>
        <xsl:apply-templates select="*[3]"/>
        <xsl:apply-templates select="Typ"/>
      </xsl:otherwise>
    </xsl:choose>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
    <xsl:if test="$mml=&quot;1&quot;">
      <xsl:element name="br"/>
    </xsl:if>
  </xsl:template>

  <xsl:template match="IdentifyWithExp">
    <xsl:variable name="nr1" select="1 + count(preceding::IdentifyWithExp)"/>
    <xsl:choose>
      <xsl:when test="$generate_items&gt;0">
        <xsl:document href="proofhtml/idreg/{$anamelc}.{$nr1}" format="html"> 
        <xsl:call-template name="iy"/>
        </xsl:document> 
        <xsl:variable name="bogus" select="1"/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="iy"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="iy">
    <xsl:if test="($mml=&quot;1&quot;) or ($generate_items&gt;0)">
      <xsl:call-template name="argtypes">
        <xsl:with-param name="el" select="Typ"/>
      </xsl:call-template>
    </xsl:if>
    <xsl:variable name="nr1" select="1 + count(preceding::IdentifyWithExp)"/>
    <xsl:element name="a">
      <xsl:attribute name="NAME">
        <xsl:value-of select="concat(&quot;IY&quot;,$nr1)"/>
      </xsl:attribute>
      <xsl:element name="b">
        <xsl:text>identify </xsl:text>
      </xsl:element>
    </xsl:element>
    <xsl:choose>
      <xsl:when test="ErrorIdentify">
        <xsl:text>erroridentify</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:choose>
          <xsl:when test="($mml=&quot;1&quot;) or ($generate_items&gt;0)">
            <xsl:apply-templates select="*[position() = last() - 1]"/>
            <xsl:element name="b">
              <xsl:text> with </xsl:text>
            </xsl:element>
            <xsl:apply-templates select="*[position() = last()]"/>
          </xsl:when>
          <xsl:otherwise>
            <xsl:for-each select="following-sibling::*[1]/Proposition/*[1]">
              <xsl:choose>
                <xsl:when test="name() = &quot;Pred&quot;">
                  <xsl:apply-templates select="*[1]"/>
                  <xsl:element name="b">
                    <xsl:text> with </xsl:text>
                  </xsl:element>
                  <xsl:apply-templates select="*[2]"/>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:choose>
                    <xsl:when test="name() = &quot;And&quot;">
                      <xsl:variable name="e1">
                        <xsl:call-template name="is_equiv">
                          <xsl:with-param name="el" select="."/>
                        </xsl:call-template>
                      </xsl:variable>
                      <xsl:choose>
                        <xsl:when test="$e1=&quot;1&quot;">
                          <xsl:apply-templates select="*[1]/*[1]/*[1]"/>
                          <xsl:element name="b">
                            <xsl:text> with </xsl:text>
                          </xsl:element>
                          <xsl:apply-templates select="*[1]/*[1]/*[2]/*[1]"/>
                        </xsl:when>
                        <xsl:otherwise>
                          <xsl:text>IDENTIFY DISPLAY FAILED -  PLEASE COMPLAIN!</xsl:text>
                          <xsl:element name="br"/>
                          <xsl:apply-templates select="."/>
                        </xsl:otherwise>
                      </xsl:choose>
                    </xsl:when>
                    <xsl:otherwise>
                      <xsl:variable name="i3">
                        <xsl:call-template name="is_impl1">
                          <xsl:with-param name="el" select="."/>
                        </xsl:call-template>
                      </xsl:variable>
                      <xsl:choose>
                        <xsl:when test="not($i3=2)">
                          <xsl:text>IDENTIFY DISPLAY FAILED -  PLEASE COMPLAIN!</xsl:text>
                        </xsl:when>
                        <xsl:otherwise>
                          <xsl:for-each select="*[1]/*[@pid=$pid_Impl_RightNot]/*[1]">
                            <xsl:choose>
                              <xsl:when test="name() = &quot;Pred&quot;">
                                <xsl:apply-templates select="*[1]"/>
                                <xsl:element name="b">
                                  <xsl:text> with </xsl:text>
                                </xsl:element>
                                <xsl:apply-templates select="*[2]"/>
                              </xsl:when>
                              <xsl:otherwise>
                                <xsl:variable name="e1">
                                  <xsl:call-template name="is_equiv">
                                    <xsl:with-param name="el" select="."/>
                                  </xsl:call-template>
                                </xsl:variable>
                                <xsl:choose>
                                  <xsl:when test="$e1=&quot;1&quot;">
                                    <xsl:apply-templates select="*[1]/*[1]/*[1]"/>
                                    <xsl:element name="b">
                                      <xsl:text> with </xsl:text>
                                    </xsl:element>
                                    <xsl:apply-templates select="*[1]/*[1]/*[2]/*[1]"/>
                                  </xsl:when>
                                  <xsl:otherwise>
                                    <xsl:text>IDENTIFY DISPLAY FAILED -  PLEASE COMPLAIN!</xsl:text>
                                    <xsl:element name="br"/>
                                    <xsl:apply-templates select="."/>
                                  </xsl:otherwise>
                                </xsl:choose>
                              </xsl:otherwise>
                            </xsl:choose>
                          </xsl:for-each>
                          <xsl:element name="b">
                            <xsl:text> when </xsl:text>
                          </xsl:element>
                          <xsl:call-template name="ilist">
                            <xsl:with-param name="separ">
                              <xsl:text>, </xsl:text>
                            </xsl:with-param>
                            <xsl:with-param name="elems" select="*[1]/*[not(@pid=$pid_Impl_RightNot)]"/>
                          </xsl:call-template>
                        </xsl:otherwise>
                      </xsl:choose>
                    </xsl:otherwise>
                  </xsl:choose>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:for-each>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
    <xsl:if test="$mml=&quot;1&quot;">
      <xsl:element name="br"/>
    </xsl:if>
  </xsl:template>

  <!-- ignore them -->
  <xsl:template match="Reservation/Typ">
    <xsl:text/>
  </xsl:template>

  <xsl:template match="Definiens/*">
    <xsl:text/>
  </xsl:template>

  <!-- xsltxt cannot use xsl:document yet, so manually insert it -->
  <!-- (now done by the perl postproc) -->
  <!-- the bogus is there to ensure that the ending xsl:doc element -->
  <!-- is printed by xslxtxt.jar too -->
  <xsl:template match="JustifiedTheorem">
    <xsl:variable name="nr1" select="1+count(preceding-sibling::JustifiedTheorem)"/>
    <xsl:choose>
      <xsl:when test="$generate_items&gt;0">
        <xsl:document href="proofhtml/th/{$anamelc}.{$nr1}" format="html"> 
        <xsl:call-template name="jt"/>
        </xsl:document> 
        <xsl:variable name="bogus" select="1"/>
      </xsl:when>
      <xsl:otherwise>
        <!-- optional interestingness rating produced by external soft -->
        <xsl:choose>
          <xsl:when test="@interesting &gt; 0">
            <!-- scale red and blue from 0% (green) to 100% (white) -->
            <xsl:variable name="intensity" select="(1 - @interesting) * 100"/>
            <xsl:element name="div">
              <xsl:attribute name="style">
                <xsl:value-of select="concat(&quot;background-color:rgb(&quot;,$intensity,&quot;%,100%,&quot;, $intensity, &quot;%);&quot;)"/>
              </xsl:attribute>
              <xsl:call-template name="jt"/>
            </xsl:element>
          </xsl:when>
          <xsl:otherwise>
            <xsl:call-template name="jt"/>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- private - assumes that is inside JustifiedTheorem -->
  <xsl:template name="jt">
    <xsl:variable name="nr1" select="1+count(preceding-sibling::JustifiedTheorem)"/>
    <xsl:element name="b">
      <xsl:text>theorem </xsl:text>
    </xsl:element>
    <xsl:choose>
      <xsl:when test="($proof_links &gt; 0) and ($print_lab_identifiers = 0)">
        <xsl:call-template name="plab1">
          <xsl:with-param name="nr" select="$nr1"/>
          <xsl:with-param name="txt">
            <xsl:text>Th</xsl:text>
          </xsl:with-param>
        </xsl:call-template>
        <xsl:text>: </xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:for-each select="Proposition[@nr &gt; 0]">
          <xsl:call-template name="pplab">
            <xsl:with-param name="nr" select="@nr"/>
            <xsl:with-param name="vid" select="@vid"/>
          </xsl:call-template>
          <xsl:text>: </xsl:text>
        </xsl:for-each>
      </xsl:otherwise>
    </xsl:choose>
    <xsl:element name="a">
      <xsl:attribute name="NAME">
        <xsl:value-of select="concat(&quot;T&quot;, $nr1)"/>
      </xsl:attribute>
      <xsl:call-template name="pcomment0">
        <xsl:with-param name="str" select="concat($aname,&quot;:&quot;, $nr1)"/>
      </xsl:call-template>
      <xsl:if test="@interesting &gt; 0">
        <xsl:text> interestingness: </xsl:text>
        <xsl:value-of select="@interesting"/>
      </xsl:if>
      <xsl:if test="$idv &gt; 0">
        <xsl:call-template name="idv_for_item">
          <xsl:with-param name="k">
            <xsl:text>t</xsl:text>
          </xsl:with-param>
          <xsl:with-param name="nr" select="$nr1"/>
        </xsl:call-template>
      </xsl:if>
      <xsl:element name="br"/>
    </xsl:element>
    <xsl:choose>
      <xsl:when test="Proof">
        <xsl:element name="div">
          <xsl:attribute name="class">
            <xsl:text>add</xsl:text>
          </xsl:attribute>
          <xsl:apply-templates select="*[1]/*[1]"/>
        </xsl:element>
        <xsl:if test="not($generate_items&gt;0) or ($generate_items_proofs&gt;0)">
          <xsl:apply-templates select="*[2]"/>
        </xsl:if>
      </xsl:when>
      <xsl:otherwise>
        <xsl:element name="div">
          <xsl:attribute name="class">
            <xsl:text>add</xsl:text>
          </xsl:attribute>
          <xsl:choose>
            <xsl:when test="Proposition/Verum">
              <xsl:element name="b">
                <xsl:text>canceled; </xsl:text>
              </xsl:element>
            </xsl:when>
            <xsl:otherwise>
              <xsl:apply-templates select="*[1]/*[1]"/>
              <xsl:text> </xsl:text>
              <xsl:apply-templates select="*[2]"/>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="idv_for_item">
    <xsl:param name="k"/>
    <xsl:param name="nr"/>
    <xsl:variable name="idv_html">
      <xsl:text>http://www.cs.miami.edu/~tptp/MizarTPTP/</xsl:text>
    </xsl:variable>
    <!-- "http://lipa.ms.mff.cuni.cz/~urban/idvtest/"; -->
    <!-- $idv_html = "file:///home/urban/mptp0.2/idvhtml/"; -->
    <xsl:variable name="tptp_file" select="concat($idv_html,&quot;problems/&quot;,$anamelc,&quot;/&quot;,$anamelc, &quot;__&quot;,$k, $nr, &quot;_&quot;, $anamelc)"/>
    <xsl:text> </xsl:text>
    <xsl:element name="img">
      <xsl:call-template name="add_hs2_attrs"/>
      <xsl:attribute name="src">
        <xsl:text>PalmTree.jpg</xsl:text>
      </xsl:attribute>
      <xsl:attribute name="title">
        <xsl:text>Show IDV graph</xsl:text>
      </xsl:attribute>
      <xsl:attribute name="alt">
        <xsl:text>Show IDV graph</xsl:text>
      </xsl:attribute>
    </xsl:element>
    <!-- <a -->
    <!-- { -->
    <!-- //    add_ajax_attrs(#u = $th); -->
    <!-- add_hs2_attrs(); -->
    <!-- @title="Show IDV graph"; -->
    <!-- <b { " IDV graph "; } -->
    <!-- } -->
    <xsl:element name="span">
      <xsl:attribute name="style">
        <xsl:text>display:none</xsl:text>
      </xsl:attribute>
      <xsl:text>:: Showing IDV graph ... (Click the Palm Tree again to close it)</xsl:text>
      <xsl:element name="APPLET">
        <xsl:attribute name="CODE">
          <xsl:text>IDVApplet.class</xsl:text>
        </xsl:attribute>
        <xsl:attribute name="ARCHIVE">
          <xsl:text>http://www.cs.miami.edu/students/strac/test/IDV/IDV.jar,http://www.cs.miami.edu/students/strac/test/IDV/TptpParser.jar,http://www.cs.miami.edu/students/strac/test/IDV/antlr-2.7.5.jar</xsl:text>
        </xsl:attribute>
        <xsl:attribute name="WIDTH">
          <xsl:text>0</xsl:text>
        </xsl:attribute>
        <xsl:attribute name="HEIGHT">
          <xsl:text>0</xsl:text>
        </xsl:attribute>
        <xsl:element name="PARAM">
          <xsl:attribute name="NAME">
            <xsl:text>URL</xsl:text>
          </xsl:attribute>
          <xsl:attribute name="VALUE">
            <xsl:value-of select="$tptp_file"/>
          </xsl:attribute>
        </xsl:element>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <xsl:template match="DefTheorem">
    <xsl:variable name="nr1" select="1+count(preceding-sibling::DefTheorem)"/>
    <xsl:choose>
      <xsl:when test="$generate_items&gt;0">
        <xsl:document href="proofhtml/def/{$anamelc}.{$nr1}" format="html"> 
        <xsl:call-template name="dt"/>
        </xsl:document> 
        <xsl:variable name="bogus" select="1"/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="dt"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- private - assumes that is inside DefTheorem -->
  <xsl:template name="dt">
    <xsl:variable name="nr1" select="1+count(preceding-sibling::DefTheorem)"/>
    <xsl:text>:: </xsl:text>
    <xsl:element name="b">
      <xsl:text>deftheorem </xsl:text>
    </xsl:element>
    <xsl:choose>
      <xsl:when test="($proof_links &gt; 0) and ($print_lab_identifiers = 0)">
        <xsl:call-template name="plab1">
          <xsl:with-param name="nr" select="$nr1"/>
          <xsl:with-param name="txt">
            <xsl:text>Def</xsl:text>
          </xsl:with-param>
        </xsl:call-template>
      </xsl:when>
      <xsl:otherwise>
        <xsl:for-each select="Proposition[@nr &gt; 0]">
          <xsl:call-template name="pplab">
            <xsl:with-param name="nr" select="@nr"/>
            <xsl:with-param name="vid" select="@vid"/>
          </xsl:call-template>
        </xsl:for-each>
      </xsl:otherwise>
    </xsl:choose>
    <xsl:text> </xsl:text>
    <!-- <a { @NAME=`concat("D",$nr1)`; -->
    <xsl:if test="@constrkind">
      <xsl:text>  defines </xsl:text>
      <xsl:call-template name="abs">
        <xsl:with-param name="k" select="@constrkind"/>
        <xsl:with-param name="nr" select="@constrnr"/>
        <xsl:with-param name="sym">
          <xsl:call-template name="abs1">
            <xsl:with-param name="k" select="@constrkind"/>
            <xsl:with-param name="nr" select="@constrnr"/>
          </xsl:call-template>
        </xsl:with-param>
      </xsl:call-template>
    </xsl:if>
    <xsl:text> </xsl:text>
    <xsl:element name="a">
      <xsl:attribute name="onclick">
        <xsl:text>hs(this)</xsl:text>
      </xsl:attribute>
      <xsl:attribute name="href">
        <xsl:text>javascript:()</xsl:text>
      </xsl:attribute>
      <xsl:value-of select="concat($aname, &quot;:def &quot;, $nr1)"/>
      <xsl:text> : </xsl:text>
      <xsl:element name="br"/>
    </xsl:element>
    <xsl:element name="span">
      <xsl:attribute name="class">
        <xsl:text>hide</xsl:text>
      </xsl:attribute>
      <xsl:element name="div">
        <xsl:attribute name="class">
          <xsl:text>add</xsl:text>
        </xsl:attribute>
        <xsl:choose>
          <xsl:when test="Proposition/Verum">
            <xsl:element name="b">
              <xsl:text>canceled; </xsl:text>
            </xsl:element>
          </xsl:when>
          <xsl:otherwise>
            <xsl:apply-templates select="*[1]/*[1]"/>
            <xsl:text>;</xsl:text>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <!-- Property, elProposition, Justification -->
  <xsl:template match="JustifiedProperty">
    <xsl:variable name="nm">
      <xsl:call-template name="lc">
        <xsl:with-param name="s" select="name(*[1])"/>
      </xsl:call-template>
    </xsl:variable>
    <xsl:element name="a">
      <xsl:call-template name="add_hs_attrs"/>
      <xsl:element name="b">
        <xsl:choose>
          <xsl:when test="$nm = &quot;antisymmetry&quot;">
            <xsl:text>asymmetry</xsl:text>
          </xsl:when>
          <xsl:otherwise>
            <xsl:value-of select="$nm"/>
          </xsl:otherwise>
        </xsl:choose>
        <xsl:text> </xsl:text>
      </xsl:element>
    </xsl:element>
    <xsl:element name="span">
      <xsl:attribute name="class">
        <xsl:text>hide</xsl:text>
      </xsl:attribute>
      <xsl:element name="br"/>
      <xsl:apply-templates select="*[2]"/>
    </xsl:element>
    <xsl:apply-templates select="*[position()&gt;2]"/>
  </xsl:template>

  <!-- Formula | ( elProposition, Justification ) -->
  <xsl:template match="UnknownCorrCond|Coherence|Compatibility|Consistency|Existence|Uniqueness">
    <xsl:element name="a">
      <xsl:call-template name="add_hs_attrs"/>
      <xsl:element name="b">
        <xsl:call-template name="lc">
          <xsl:with-param name="s" select="name()"/>
        </xsl:call-template>
        <xsl:text> </xsl:text>
      </xsl:element>
    </xsl:element>
    <xsl:element name="span">
      <xsl:attribute name="class">
        <xsl:text>hide</xsl:text>
      </xsl:attribute>
      <xsl:element name="br"/>
      <xsl:apply-templates select="*[1]"/>
    </xsl:element>
    <xsl:choose>
      <xsl:when test="count(*)&gt;1">
        <xsl:apply-templates select="*[position()&gt;1]"/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:text>;</xsl:text>
        <xsl:element name="br"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- CorrectnessCondition*, elProposition, Justification -->
  <xsl:template match="Correctness">
    <xsl:element name="a">
      <xsl:call-template name="add_hs_attrs"/>
      <xsl:element name="b">
        <xsl:text>correctness </xsl:text>
      </xsl:element>
    </xsl:element>
    <!-- apply to subconditions , skip their conjunction -->
    <xsl:element name="span">
      <xsl:attribute name="class">
        <xsl:text>hide</xsl:text>
      </xsl:attribute>
      <xsl:element name="br"/>
      <xsl:apply-templates select="*[position()&lt;(last()-1)]"/>
    </xsl:element>
    <xsl:apply-templates select="*[position()=last()]"/>
  </xsl:template>

  <xsl:template match="Canceled">
    <xsl:element name="b">
      <xsl:text>canceled;</xsl:text>
    </xsl:element>
    <xsl:element name="br"/>
  </xsl:template>

  <xsl:template match="SchemeFuncDecl">
    <xsl:call-template name="pschfvar">
      <xsl:with-param name="nr" select="@nr"/>
    </xsl:call-template>
    <xsl:text>(</xsl:text>
    <xsl:call-template name="list">
      <xsl:with-param name="separ">
        <xsl:text>,</xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="ArgTypes/Typ"/>
    </xsl:call-template>
    <xsl:text>) </xsl:text>
    <xsl:element name="b">
      <xsl:text>-&gt; </xsl:text>
    </xsl:element>
    <xsl:apply-templates select="*[2]"/>
  </xsl:template>

  <xsl:template match="SchemePredDecl">
    <xsl:call-template name="pschpvar">
      <xsl:with-param name="nr" select="@nr"/>
    </xsl:call-template>
    <xsl:text>[</xsl:text>
    <xsl:call-template name="list">
      <xsl:with-param name="separ">
        <xsl:text>,</xsl:text>
      </xsl:with-param>
      <xsl:with-param name="elems" select="ArgTypes/Typ"/>
    </xsl:call-template>
    <xsl:text>]</xsl:text>
  </xsl:template>

  <!-- ( elSchemeFuncDecl | elSchemePredDecl )*, -->
  <!-- element elSchemePremises { elProposition* }, -->
  <!-- elProposition, Justification, elEndPosition -->
  <xsl:template match="SchemeBlock">
    <xsl:choose>
      <xsl:when test="$generate_items&gt;0">
        <xsl:document href="proofhtml/sch/{$anamelc}.{@schemenr}" format="html"> 
        <xsl:call-template name="sd"/>
        </xsl:document> 
        <xsl:variable name="bogus" select="1"/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="sd"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="sd">
    <xsl:element name="div">
      <xsl:element name="a">
        <xsl:attribute name="NAME">
          <xsl:value-of select="concat(&quot;S&quot;,@schemenr)"/>
        </xsl:attribute>
        <xsl:element name="b">
          <xsl:text>scheme  </xsl:text>
        </xsl:element>
        <xsl:call-template name="pcomment">
          <xsl:with-param name="str" select="concat($aname,&quot;:sch &quot;,@schemenr)"/>
        </xsl:call-template>
      </xsl:element>
      <!-- "s"; `@schemenr`; -->
      <xsl:choose>
        <xsl:when test="($proof_links &gt; 0) and ($print_lab_identifiers = 0)">
          <xsl:call-template name="plab1">
            <xsl:with-param name="nr" select="@schemenr"/>
            <xsl:with-param name="txt">
              <xsl:text>Sch</xsl:text>
            </xsl:with-param>
          </xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
          <xsl:call-template name="pplab">
            <xsl:with-param name="nr" select="@schemenr"/>
            <xsl:with-param name="vid" select="@vid"/>
            <xsl:with-param name="txt">
              <xsl:text>Sch</xsl:text>
            </xsl:with-param>
          </xsl:call-template>
        </xsl:otherwise>
      </xsl:choose>
      <xsl:text>{ </xsl:text>
      <xsl:call-template name="list">
        <xsl:with-param name="separ">
          <xsl:text>, </xsl:text>
        </xsl:with-param>
        <xsl:with-param name="elems" select="SchemeFuncDecl|SchemePredDecl"/>
      </xsl:call-template>
      <xsl:text> } :</xsl:text>
      <xsl:element name="br"/>
      <xsl:element name="div">
        <xsl:attribute name="class">
          <xsl:text>add</xsl:text>
        </xsl:attribute>
        <xsl:apply-templates select="Proposition"/>
      </xsl:element>
      <xsl:if test="SchemePremises/Proposition">
        <xsl:element name="b">
          <xsl:text>provided</xsl:text>
        </xsl:element>
        <xsl:element name="div">
          <xsl:attribute name="class">
            <xsl:text>add</xsl:text>
          </xsl:attribute>
          <xsl:call-template name="andlist">
            <xsl:with-param name="elems" select="SchemePremises/Proposition"/>
          </xsl:call-template>
        </xsl:element>
      </xsl:if>
      <xsl:if test="not($generate_items&gt;0)">
        <xsl:apply-templates select="*[position() = last() - 1]"/>
      </xsl:if>
    </xsl:element>
  </xsl:template>

  <!-- ( ( CorrectnessCondition*, elCorrectness?, -->
  <!-- elJustifiedProperty*, elConstructor?, elPattern? ) -->
  <!-- | ( elConstructor, elConstructor, elConstructor+, -->
  <!-- elRegistration, CorrectnessCondition*, -->
  <!-- elCorrectness?, elPattern+ )) -->
  <!-- ##TODO: commented registration and strict attr for defstruct -->
  <xsl:template match="Definition">
    <xsl:choose>
      <xsl:when test="@expandable = &quot;true&quot;">
        <xsl:variable name="argtypes" select="../Let/Typ"/>
        <xsl:variable name="loci">
          <xsl:choose>
            <xsl:when test="($mml=&quot;1&quot;) or ($generate_items&gt;0)">
              <xsl:text>1</xsl:text>
            </xsl:when>
            <xsl:otherwise>
              <xsl:text>2</xsl:text>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:variable>
        <xsl:for-each select="Pattern">
          <xsl:element name="a">
            <xsl:attribute name="NAME">
              <xsl:value-of select="concat(&quot;NM&quot;, @nr)"/>
            </xsl:attribute>
            <xsl:element name="b">
              <xsl:text>mode </xsl:text>
            </xsl:element>
            <xsl:call-template name="abs1">
              <xsl:with-param name="k">
                <xsl:text>M</xsl:text>
              </xsl:with-param>
              <xsl:with-param name="fnr" select="@formatnr"/>
            </xsl:call-template>
            <xsl:if test="Visible/Int">
              <xsl:text> of </xsl:text>
              <xsl:for-each select="Visible/Int">
                <xsl:variable name="x" select="@x"/>
                <xsl:choose>
                  <xsl:when test="$loci=&quot;2&quot;">
                    <xsl:call-template name="ppconst">
                      <xsl:with-param name="nr" select="$x"/>
                      <xsl:with-param name="vid" select="$argtypes[position()=$x]/@vid"/>
                    </xsl:call-template>
                  </xsl:when>
                  <xsl:otherwise>
                    <xsl:call-template name="ploci">
                      <xsl:with-param name="nr" select="$x"/>
                    </xsl:call-template>
                  </xsl:otherwise>
                </xsl:choose>
                <xsl:if test="not(position()=last())">
                  <xsl:text>,</xsl:text>
                </xsl:if>
              </xsl:for-each>
            </xsl:if>
            <xsl:element name="b">
              <xsl:text> is </xsl:text>
            </xsl:element>
          </xsl:element>
          <xsl:apply-templates select="Expansion/Typ"/>
          <xsl:text>;</xsl:text>
          <xsl:element name="br"/>
        </xsl:for-each>
      </xsl:when>
      <xsl:otherwise>
        <!-- @nr is present iff Definiens is present; it can be 0 if -->
        <!-- the definiens is not labeled, otherwise it is the proposition number -->
        <!-- of its deftheorem -->
        <xsl:choose>
          <xsl:when test="@nr and ($generate_items&gt;0)">
            <xsl:variable name="cnt1" select="1 + count(preceding-sibling::Definition[@nr])"/>
            <xsl:variable name="defnr" select="../following-sibling::Definiens[position() = $cnt1]/@defnr"/>
            <xsl:document href="proofhtml/dfs/{$anamelc}.{$defnr}" format="html"> 
            <xsl:call-template name="dfs"/>
            </xsl:document> 
            <xsl:variable name="bogus" select="1"/>
          </xsl:when>
          <xsl:otherwise>
            <xsl:call-template name="dfs"/>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
    <xsl:apply-templates select="*[not((name()=&apos;Constructor&apos;) or (name()=&apos;Pattern&apos;) 
                or (name()=&apos;Registration&apos;))]"/>
  </xsl:template>

  <xsl:template name="dfs">
    <xsl:variable name="nl">
      <xsl:choose>
        <xsl:when test="@nr">
          <xsl:text>0</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>1</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="argtypes" select="../Let/Typ"/>
    <!-- Constructor may be missing, if this is a redefinition -->
    <!-- that does not change its types. In that case, the Constructor needs -->
    <!-- to be retrieved from the Definiens - see below. -->
    <xsl:if test="not(@nr)">
      <!-- for generate_items, we have to take loci from the constructor here -->
      <xsl:variable name="indef1">
        <xsl:choose>
          <xsl:when test="($generate_items &gt; 0)">
            <xsl:text>0</xsl:text>
          </xsl:when>
          <xsl:otherwise>
            <xsl:text>1</xsl:text>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:variable>
      <xsl:apply-templates select="Constructor">
        <xsl:with-param name="indef" select="$indef1"/>
        <xsl:with-param name="nl" select="$nl"/>
        <xsl:with-param name="argt" select="$argtypes"/>
      </xsl:apply-templates>
    </xsl:if>
    <!-- @nr is present iff Definiens is present; it can be 0 if -->
    <!-- the deiniens is not labeled, otherwise it is the proposition number -->
    <!-- of its deftheorem -->
    <xsl:if test="@nr">
      <xsl:variable name="nr1" select="@nr"/>
      <xsl:variable name="vid" select="@vid"/>
      <xsl:variable name="cnt1" select="1 + count(preceding-sibling::Definition[@nr])"/>
      <xsl:variable name="cnstr" select="count(Constructor)"/>
      <xsl:if test="($generate_items &gt; 0)">
        <!-- Definiens is better than Constructor for loci display, -->
        <!-- since Constructor may be missing for redefinitions. -->
        <xsl:for-each select="../following-sibling::Definiens[position() = $cnt1]">
          <xsl:call-template name="argtypes">
            <xsl:with-param name="el" select="Typ"/>
          </xsl:call-template>
        </xsl:for-each>
      </xsl:if>
      <xsl:apply-templates select="Constructor">
        <xsl:with-param name="indef">
          <xsl:text>1</xsl:text>
        </xsl:with-param>
        <xsl:with-param name="nl" select="$nl"/>
        <xsl:with-param name="argt" select="$argtypes"/>
      </xsl:apply-templates>
      <xsl:for-each select="../following-sibling::Definiens[position() = $cnt1]">
        <xsl:variable name="ckind" select="@constrkind"/>
        <xsl:variable name="cnr" select="@constrnr"/>
        <xsl:if test="$cnstr = 0">
          <!-- here the redefined constructor is retrieved from definiens -->
          <xsl:element name="b">
            <xsl:text>redefine </xsl:text>
          </xsl:element>
          <xsl:variable name="doc">
            <xsl:choose>
              <xsl:when test="key($ckind, $cnr)">
                <xsl:text/>
              </xsl:when>
              <xsl:otherwise>
                <xsl:value-of select="$constrs"/>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:variable>
          <xsl:for-each select="document($doc, /)">
            <xsl:apply-templates select="key($ckind, $cnr)">
              <xsl:with-param name="indef">
                <xsl:text>1</xsl:text>
              </xsl:with-param>
              <xsl:with-param name="nl" select="$nl"/>
              <xsl:with-param name="argt" select="$argtypes"/>
              <xsl:with-param name="nrt">
                <xsl:text>1</xsl:text>
              </xsl:with-param>
            </xsl:apply-templates>
          </xsl:for-each>
        </xsl:if>
        <xsl:element name="b">
          <xsl:choose>
            <xsl:when test="DefMeaning/@kind = &apos;e&apos;">
              <xsl:text> equals </xsl:text>
            </xsl:when>
            <xsl:otherwise>
              <xsl:text> means </xsl:text>
            </xsl:otherwise>
          </xsl:choose>
        </xsl:element>
        <xsl:if test="$nr1 &gt; 0">
          <xsl:text>:</xsl:text>
          <xsl:choose>
            <xsl:when test="($proof_links &gt; 0) and ($print_lab_identifiers = 0)">
              <xsl:call-template name="plab1">
                <xsl:with-param name="nr" select="@defnr"/>
                <xsl:with-param name="txt">
                  <xsl:text>Def</xsl:text>
                </xsl:with-param>
              </xsl:call-template>
            </xsl:when>
            <xsl:otherwise>
              <xsl:call-template name="pplab">
                <xsl:with-param name="nr" select="$nr1"/>
                <xsl:with-param name="vid" select="$vid"/>
              </xsl:call-template>
            </xsl:otherwise>
          </xsl:choose>
          <xsl:text>: </xsl:text>
        </xsl:if>
        <xsl:element name="a">
          <xsl:attribute name="NAME">
            <xsl:value-of select="concat(&quot;D&quot;, @defnr)"/>
          </xsl:attribute>
          <xsl:call-template name="pcomment">
            <xsl:with-param name="str" select="concat($aname, &quot;:def &quot;, @defnr)"/>
          </xsl:call-template>
        </xsl:element>
        <!-- note that loci below can be translated to constants and identifiers -->
        <!-- - see definition of LocusVar -->
        <xsl:for-each select="DefMeaning/PartialDef">
          <xsl:apply-templates select="*[1]"/>
          <xsl:element name="b">
            <xsl:text> if </xsl:text>
          </xsl:element>
          <xsl:apply-templates select="*[2]"/>
          <xsl:element name="br"/>
        </xsl:for-each>
        <xsl:if test="(DefMeaning/PartialDef) 
	    and (DefMeaning/*[(position() = last()) 
		and not(name()=&quot;PartialDef&quot;)])">
          <xsl:element name="b">
            <xsl:text> otherwise </xsl:text>
          </xsl:element>
        </xsl:if>
        <xsl:apply-templates select="DefMeaning/*[(position() = last()) and not(name()=&quot;PartialDef&quot;)]"/>
        <xsl:text>;</xsl:text>
        <xsl:element name="br"/>
      </xsl:for-each>
    </xsl:if>
  </xsl:template>

  <!-- ( elLet | elAssume | elGiven | AuxiliaryItem | -->
  <!-- elCanceled | elDefinition )*, elEndPosition -->
  <xsl:template match="DefinitionBlock">
    <xsl:element name="div">
      <xsl:element name="b">
        <xsl:text>definition</xsl:text>
      </xsl:element>
      <xsl:element name="div">
        <xsl:attribute name="class">
          <xsl:text>add</xsl:text>
        </xsl:attribute>
        <xsl:apply-templates select="*[not(name()=&apos;EndPosition&apos;)]"/>
      </xsl:element>
      <xsl:element name="b">
        <xsl:text>end;</xsl:text>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <!-- ( elRCluster | elFCluster | elCCluster ), -->
  <!-- CorrectnessCondition*, elCorrectness? -->
  <xsl:template match="Registration">
    <xsl:apply-templates/>
  </xsl:template>

  <!-- elIdentifyWithExp, CorrectnessCondition*, elCorrectness? -->
  <xsl:template match="IdentifyRegistration">
    <xsl:apply-templates/>
  </xsl:template>

  <!-- ( elLet | AuxiliaryItem | elRegistration | elCanceled )+, elEndPosition -->
  <xsl:template match="RegistrationBlock">
    <xsl:element name="div">
      <xsl:element name="b">
        <xsl:text>registration</xsl:text>
      </xsl:element>
      <xsl:element name="div">
        <xsl:attribute name="class">
          <xsl:text>add</xsl:text>
        </xsl:attribute>
        <xsl:apply-templates select="*[not(name()=&apos;EndPosition&apos;)]"/>
      </xsl:element>
      <xsl:element name="b">
        <xsl:text>end;</xsl:text>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <xsl:template match="NotationBlock">
    <xsl:element name="div">
      <xsl:element name="b">
        <xsl:text>notation</xsl:text>
      </xsl:element>
      <xsl:element name="div">
        <xsl:attribute name="class">
          <xsl:text>add</xsl:text>
        </xsl:attribute>
        <xsl:apply-templates select="*[not(name()=&apos;EndPosition&apos;)]"/>
      </xsl:element>
      <xsl:element name="b">
        <xsl:text>end;</xsl:text>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <!-- Blocks -->
  <xsl:template match="BlockThesis"/>

  <!-- "blockthesis: "; apply; ";"; <br; } -->
  <!-- (  ( elBlockThesis, elCase, elThesis, Reasoning ) -->
  <!-- |  ( elCase, Reasoning, elBlockThesis ) ) -->
  <xsl:template match="CaseBlock">
    <xsl:element name="div">
      <xsl:element name="a">
        <xsl:call-template name="add_hsNdiv_attrs"/>
        <xsl:if test="$proof_links&gt;0">
          <xsl:attribute name="title">
            <xsl:value-of select="@newlevel"/>
          </xsl:attribute>
        </xsl:if>
        <xsl:element name="b">
          <xsl:text>case </xsl:text>
        </xsl:element>
      </xsl:element>
      <xsl:apply-templates select="Case"/>
      <xsl:element name="div">
        <xsl:attribute name="class">
          <xsl:text>add</xsl:text>
        </xsl:attribute>
        <xsl:apply-templates select="*[not(name()=&apos;Case&apos;)]"/>
      </xsl:element>
      <xsl:element name="b">
        <xsl:text>end;</xsl:text>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <xsl:template match="SupposeBlock">
    <xsl:element name="div">
      <xsl:element name="a">
        <xsl:call-template name="add_hsNdiv_attrs"/>
        <xsl:if test="$proof_links&gt;0">
          <xsl:attribute name="title">
            <xsl:value-of select="@newlevel"/>
          </xsl:attribute>
        </xsl:if>
        <xsl:element name="b">
          <xsl:text>suppose </xsl:text>
        </xsl:element>
      </xsl:element>
      <xsl:apply-templates select="Suppose"/>
      <xsl:element name="div">
        <xsl:attribute name="class">
          <xsl:text>add</xsl:text>
        </xsl:attribute>
        <xsl:apply-templates select="*[not(name()=&apos;Suppose&apos;)]"/>
      </xsl:element>
      <xsl:element name="b">
        <xsl:text>end;</xsl:text>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <!-- (  ( elBlockThesis, ( elCaseBlock+ | elSupposeBlock+ ), -->
  <!-- elPerCases, elThesis, elEndPosition  ) -->
  <!-- |  ( ( elCaseBlock+ | elSupposeBlock+ ), -->
  <!-- elPerCases, elEndPosition, elBlockThesis ) ) -->
  <xsl:template match="PerCasesReasoning">
    <xsl:element name="div">
      <xsl:element name="a">
        <xsl:call-template name="add_hsNdiv_attrs"/>
        <xsl:if test="$proof_links&gt;0">
          <xsl:attribute name="title">
            <xsl:value-of select="@newlevel"/>
          </xsl:attribute>
        </xsl:if>
        <xsl:element name="b">
          <xsl:text>per </xsl:text>
        </xsl:element>
      </xsl:element>
      <xsl:apply-templates select="PerCases"/>
      <xsl:element name="div">
        <xsl:attribute name="class">
          <xsl:text>add</xsl:text>
        </xsl:attribute>
        <xsl:apply-templates select="BlockThesis"/>
        <xsl:apply-templates select="Thesis"/>
        <xsl:apply-templates select="CaseBlock | SupposeBlock"/>
      </xsl:element>
      <xsl:element name="b">
        <xsl:text>end;</xsl:text>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <!-- elBlockThesis, Reasoning -->
  <!-- the Proof is done in two parts, as a preparation for printing -->
  <!-- top proofs into separate documents, and their loading via AJAX -->
  <!-- this is a non-top-level proof -->
  <xsl:template match="Proof/Proof | Now/Proof | Conclusion/Proof | CaseBlock/Proof | SupposeBlock/Proof">
    <xsl:element name="div">
      <xsl:element name="a">
        <xsl:call-template name="add_hs2_attrs"/>
        <xsl:if test="$proof_links&gt;0">
          <xsl:attribute name="title">
            <xsl:value-of select="@newlevel"/>
          </xsl:attribute>
        </xsl:if>
        <xsl:element name="b">
          <xsl:text>proof </xsl:text>
        </xsl:element>
      </xsl:element>
      <xsl:element name="div">
        <xsl:attribute name="class">
          <xsl:text>add</xsl:text>
        </xsl:attribute>
        <xsl:apply-templates/>
      </xsl:element>
      <xsl:element name="b">
        <xsl:text>end;</xsl:text>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <!-- hence the rest is a top-level proof -->
  <!-- xsltxt cannot use xsl:document yet, so manually insert -->
  <!-- (now done as perl postproc) -->
  <!-- if you want ajax_proofs -->
  <xsl:template match="Proof">
    <xsl:variable name="nm" select="concat($ajax_proof_dir,&quot;/&quot;,$anamelc,&quot;/&quot;,@newlevel)"/>
    <xsl:element name="div">
      <xsl:element name="a">
        <xsl:choose>
          <xsl:when test="$ajax_proofs&gt;0">
            <xsl:call-template name="add_ajax_attrs">
              <xsl:with-param name="u" select="$nm"/>
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <xsl:call-template name="add_hs2_attrs"/>
          </xsl:otherwise>
        </xsl:choose>
        <xsl:if test="$proof_links&gt;0">
          <xsl:attribute name="title">
            <xsl:value-of select="@newlevel"/>
          </xsl:attribute>
        </xsl:if>
        <xsl:element name="b">
          <xsl:text>proof </xsl:text>
        </xsl:element>
      </xsl:element>
      <xsl:choose>
        <xsl:when test="$ajax_proofs&gt;0">
          <xsl:element name="span"/>
          <xsl:document href="{$ajax_proof_dir}/{$anamelc}/{@newlevel}" format="html"> 
          <xsl:element name="div">
            <xsl:attribute name="class">
              <xsl:text>add</xsl:text>
            </xsl:attribute>
            <xsl:apply-templates/>
          </xsl:element>
          </xsl:document> 
          <xsl:variable name="bogus" select="1"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:element name="div">
            <xsl:attribute name="class">
              <xsl:text>add</xsl:text>
            </xsl:attribute>
            <xsl:apply-templates/>
          </xsl:element>
        </xsl:otherwise>
      </xsl:choose>
      <xsl:element name="b">
        <xsl:text>end;</xsl:text>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <!-- Reasoning, elBlockThesis -->
  <!-- #nkw tells not to print the keyword (used if hereby was printed above) -->
  <!-- ###TODO: fix for generating items (see Proposition) -->
  <xsl:template match="Now">
    <xsl:param name="nkw"/>
    <xsl:choose>
      <xsl:when test="not($nkw=&quot;1&quot;)">
        <xsl:element name="div">
          <xsl:if test="@nr&gt;0">
            <xsl:call-template name="pplab">
              <xsl:with-param name="nr" select="@nr"/>
              <xsl:with-param name="vid" select="@vid"/>
            </xsl:call-template>
            <xsl:text>: </xsl:text>
          </xsl:if>
          <xsl:element name="a">
            <xsl:call-template name="add_hs2_attrs"/>
            <xsl:if test="$proof_links&gt;0">
              <xsl:attribute name="title">
                <xsl:value-of select="@newlevel"/>
              </xsl:attribute>
            </xsl:if>
            <xsl:element name="b">
              <xsl:text>now </xsl:text>
            </xsl:element>
          </xsl:element>
          <xsl:call-template name="now_body"/>
          <xsl:element name="b">
            <xsl:text>end;</xsl:text>
          </xsl:element>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:call-template name="now_body"/>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <xsl:template name="now_body">
    <xsl:element name="div">
      <xsl:attribute name="class">
        <xsl:text>add</xsl:text>
      </xsl:attribute>
      <xsl:apply-templates select="BlockThesis"/>
      <xsl:apply-templates select="*[not(name()=&apos;BlockThesis&apos;)]"/>
    </xsl:element>
  </xsl:template>

  <xsl:template name="idv_for_top">
    <xsl:variable name="idv_html">
      <xsl:text>http://lipa.ms.mff.cuni.cz/~urban/idvtest/</xsl:text>
    </xsl:variable>
    <!-- $idv_html = "file:///home/urban/mptp0.2/idvhtml/"; -->
    <xsl:variable name="tptp_file" select="concat($idv_html,&quot;top/&quot;,$anamelc,&quot;.top.rated&quot;)"/>
    <xsl:text> </xsl:text>
    <xsl:element name="img">
      <xsl:call-template name="add_hs2_attrs"/>
      <xsl:attribute name="src">
        <xsl:text>hammock.jpg</xsl:text>
      </xsl:attribute>
      <xsl:attribute name="title">
        <xsl:text>Show IDV graph for whole article</xsl:text>
      </xsl:attribute>
      <xsl:attribute name="alt">
        <xsl:text>Show IDV graph for whole article</xsl:text>
      </xsl:attribute>
    </xsl:element>
    <!-- <a -->
    <!-- { -->
    <!-- //    add_ajax_attrs(#u = $th); -->
    <!-- add_hs2_attrs(); -->
    <!-- @title="Show IDV graph"; -->
    <!-- <b { " IDV graph "; } -->
    <!-- } -->
    <xsl:element name="span">
      <xsl:attribute name="style">
        <xsl:text>display:none</xsl:text>
      </xsl:attribute>
      <xsl:text>:: Showing IDV graph ... (Click the Palm Trees again to close it)</xsl:text>
      <xsl:element name="APPLET">
        <xsl:attribute name="CODE">
          <xsl:text>IDVApplet.class</xsl:text>
        </xsl:attribute>
        <xsl:attribute name="ARCHIVE">
          <xsl:text>IDV.jar,TptpParser.jar,antlr-2.7.5.jar</xsl:text>
        </xsl:attribute>
        <xsl:attribute name="WIDTH">
          <xsl:text>0</xsl:text>
        </xsl:attribute>
        <xsl:attribute name="HEIGHT">
          <xsl:text>0</xsl:text>
        </xsl:attribute>
        <xsl:element name="PARAM">
          <xsl:attribute name="NAME">
            <xsl:text>URL</xsl:text>
          </xsl:attribute>
          <xsl:attribute name="VALUE">
            <xsl:value-of select="$tptp_file"/>
          </xsl:attribute>
        </xsl:element>
      </xsl:element>
    </xsl:element>
  </xsl:template>

  <!-- tpl [Now](#nkw) { -->
  <!-- <div { <b { if [not($nkw="1")] { "now ";} } -->
  <!-- <div { @class="add"; apply[BlockThesis]; -->
  <!-- apply[*[not(name()='BlockThesis')]]; } -->
  <!-- <b { "end;"; } } } -->
  <!-- separate top-level items by additional newline -->
  <xsl:template match="Article">
    <xsl:element name="div">
      <xsl:call-template name="pcomment0">
        <xsl:with-param name="str" select="concat($aname, &quot;  semantic presentation&quot;)"/>
      </xsl:call-template>
      <xsl:if test="$idv &gt; 0">
        <xsl:call-template name="idv_for_top"/>
      </xsl:if>
    </xsl:element>
    <xsl:element name="br"/>
    <xsl:for-each select="*">
      <xsl:apply-templates select="."/>
      <xsl:if test="(not(name()=&apos;Definiens&apos;)) and (not(name()=&apos;Reservation&apos;))">
        <xsl:element name="br"/>
      </xsl:if>
    </xsl:for-each>
  </xsl:template>

  <!-- processing of imported documents -->
  <xsl:template match="Theorem">
    <xsl:element name="b">
      <xsl:text>theorem </xsl:text>
    </xsl:element>
    <xsl:call-template name="mkref">
      <xsl:with-param name="aid" select="@aid"/>
      <xsl:with-param name="nr" select="@nr"/>
      <xsl:with-param name="k" select="@kind"/>
    </xsl:call-template>
    <xsl:element name="br"/>
    <xsl:choose>
      <xsl:when test="Verum">
        <xsl:element name="b">
          <xsl:text>canceled; </xsl:text>
        </xsl:element>
      </xsl:when>
      <xsl:otherwise>
        <xsl:apply-templates/>
      </xsl:otherwise>
    </xsl:choose>
    <xsl:element name="br"/>
    <xsl:element name="br"/>
  </xsl:template>

  <!-- now used only when #mml=1 - in article the block has them -->
  <xsl:template match="ArgTypes">
    <xsl:call-template name="argtypes">
      <xsl:with-param name="el" select="*"/>
    </xsl:call-template>
  </xsl:template>

  <xsl:template name="argtypes">
    <xsl:param name="el"/>
    <xsl:if test="$el">
      <xsl:element name="b">
        <xsl:text>let </xsl:text>
      </xsl:element>
      <xsl:call-template name="ploci">
        <xsl:with-param name="nr">
          <xsl:text>1</xsl:text>
        </xsl:with-param>
      </xsl:call-template>
      <xsl:text> be </xsl:text>
      <xsl:call-template name="alist">
        <xsl:with-param name="j">
          <xsl:text>1</xsl:text>
        </xsl:with-param>
        <xsl:with-param name="sep1">
          <xsl:text>, </xsl:text>
        </xsl:with-param>
        <xsl:with-param name="sep2">
          <xsl:text> be </xsl:text>
        </xsl:with-param>
        <xsl:with-param name="elems" select="$el"/>
      </xsl:call-template>
      <xsl:text>;</xsl:text>
      <xsl:element name="br"/>
    </xsl:if>
  </xsl:template>

  <!-- #indef tells not to use Argtypes (we are inside Definition) -->
  <!-- note that this can also be used for displaying -->
  <!-- environmental constructors, or constructor retrieved from other file -->
  <!-- #argt is explicit list of argument types, useful for -->
  <!-- getting the @vid (identifier numbers) of loci -->
  <!-- #nrt tells not to showthe result type(s) -->
  <xsl:template match="Constructor">
    <xsl:param name="indef"/>
    <xsl:param name="nl"/>
    <xsl:param name="argt"/>
    <xsl:param name="nrt"/>
    <xsl:variable name="loci">
      <xsl:choose>
        <xsl:when test="($mml=&quot;1&quot;) or ($generate_items&gt;0)">
          <xsl:text>1</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>2</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:if test="not($indef=&quot;1&quot;)">
      <xsl:apply-templates select="ArgTypes"/>
    </xsl:if>
    <xsl:if test="@redefnr&gt;0">
      <xsl:call-template name="pcomment0">
        <xsl:with-param name="str">
          <xsl:text>original: </xsl:text>
        </xsl:with-param>
      </xsl:call-template>
      <xsl:call-template name="abs">
        <xsl:with-param name="k" select="@kind"/>
        <xsl:with-param name="nr" select="@redefnr"/>
        <xsl:with-param name="sym">
          <xsl:call-template name="abs1">
            <xsl:with-param name="k" select="@kind"/>
            <xsl:with-param name="nr" select="@redefnr"/>
          </xsl:call-template>
        </xsl:with-param>
      </xsl:call-template>
      <xsl:element name="br"/>
      <xsl:element name="b">
        <xsl:text>redefine </xsl:text>
      </xsl:element>
    </xsl:if>
    <xsl:element name="a">
      <xsl:attribute name="NAME">
        <xsl:value-of select="concat(@kind,@nr)"/>
      </xsl:attribute>
      <xsl:element name="b">
        <xsl:call-template name="mkind">
          <xsl:with-param name="kind" select="@kind"/>
        </xsl:call-template>
      </xsl:element>
      <xsl:text> </xsl:text>
    </xsl:element>
    <xsl:choose>
      <xsl:when test="@kind=&quot;G&quot;">
        <xsl:call-template name="abs">
          <xsl:with-param name="k" select="@kind"/>
          <xsl:with-param name="nr" select="@relnr"/>
          <xsl:with-param name="sym">
            <xsl:call-template name="abs1">
              <xsl:with-param name="k" select="@kind"/>
              <xsl:with-param name="nr" select="@relnr"/>
            </xsl:call-template>
          </xsl:with-param>
        </xsl:call-template>
        <xsl:text>(# </xsl:text>
        <xsl:for-each select="Fields/Field">
          <xsl:call-template name="abs">
            <xsl:with-param name="k">
              <xsl:text>U</xsl:text>
            </xsl:with-param>
            <xsl:with-param name="nr" select="@nr"/>
            <xsl:with-param name="sym">
              <xsl:call-template name="abs1">
                <xsl:with-param name="k">
                  <xsl:text>U</xsl:text>
                </xsl:with-param>
                <xsl:with-param name="nr" select="@nr"/>
              </xsl:call-template>
            </xsl:with-param>
          </xsl:call-template>
          <xsl:if test="not(position()=last())">
            <xsl:text>, </xsl:text>
          </xsl:if>
        </xsl:for-each>
        <xsl:text> #)</xsl:text>
      </xsl:when>
      <xsl:otherwise>
        <xsl:choose>
          <xsl:when test="@kind=&apos;V&apos;">
            <xsl:variable name="nr1" select="count(ArgTypes/Typ)"/>
            <xsl:choose>
              <xsl:when test="$loci = 1">
                <xsl:call-template name="ploci">
                  <xsl:with-param name="nr" select="$nr1"/>
                </xsl:call-template>
              </xsl:when>
              <xsl:otherwise>
                <xsl:call-template name="ppconst">
                  <xsl:with-param name="nr" select="$nr1"/>
                  <xsl:with-param name="vid" select="$argt[position() = $nr1]/@vid"/>
                </xsl:call-template>
              </xsl:otherwise>
            </xsl:choose>
            <xsl:text> is </xsl:text>
            <xsl:call-template name="abs">
              <xsl:with-param name="k" select="@kind"/>
              <xsl:with-param name="nr" select="@relnr"/>
              <xsl:with-param name="sym">
                <xsl:call-template name="abs1">
                  <xsl:with-param name="k" select="@kind"/>
                  <xsl:with-param name="nr" select="@relnr"/>
                </xsl:call-template>
              </xsl:with-param>
            </xsl:call-template>
          </xsl:when>
          <xsl:otherwise>
            <xsl:call-template name="pp">
              <xsl:with-param name="k" select="@kind"/>
              <xsl:with-param name="nr" select="@relnr"/>
              <xsl:with-param name="args" select="$argt"/>
              <xsl:with-param name="loci" select="$loci"/>
            </xsl:call-template>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:otherwise>
    </xsl:choose>
    <xsl:if test="not($nrt = 1) and 
        ((@kind = &apos;M&apos;) or (@kind = &apos;K&apos;) or (@kind= &apos;G&apos;) 
         or (@kind= &apos;U&apos;) or (@kind= &apos;L&apos;))">
      <xsl:element name="b">
        <xsl:text> -&gt; </xsl:text>
      </xsl:element>
      <!-- note that loci in Typs here can be translated to constants and identifiers -->
      <!-- - see definition of LocusVar -->
      <xsl:call-template name="list">
        <xsl:with-param name="separ">
          <xsl:text>,</xsl:text>
        </xsl:with-param>
        <xsl:with-param name="elems" select="Typ"/>
      </xsl:call-template>
    </xsl:if>
    <xsl:choose>
      <xsl:when test="not($indef=&quot;1&quot;)">
        <xsl:text>;</xsl:text>
        <xsl:element name="br"/>
        <xsl:element name="br"/>
      </xsl:when>
      <xsl:otherwise>
        <xsl:if test="$nl=&quot;1&quot;">
          <xsl:text>;</xsl:text>
          <xsl:element name="br"/>
        </xsl:if>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- display synonym and antonym definiiotns -->
  <xsl:template match="NotationBlock/Pattern">
    <!-- pp1(#k=`@constrkind`,#nr=`@constrnr`,#vis=`Visible/Int`, -->
    <!-- #fnr=`@formatnr`, #loci="1"); <br; -->
    <xsl:variable name="loci">
      <xsl:choose>
        <xsl:when test="$mml=&quot;1&quot;">
          <xsl:text>1</xsl:text>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>2</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:variable>
    <xsl:variable name="argtypes" select="../Let/Typ"/>
    <xsl:element name="a">
      <xsl:attribute name="NAME">
        <xsl:value-of select="concat(&quot;N&quot;,@kind,@nr)"/>
      </xsl:attribute>
      <xsl:element name="b">
        <xsl:choose>
          <xsl:when test="@antonymic">
            <xsl:text>antonym </xsl:text>
          </xsl:when>
          <xsl:otherwise>
            <xsl:text>synonym </xsl:text>
          </xsl:otherwise>
        </xsl:choose>
      </xsl:element>
      <xsl:call-template name="pp1">
        <xsl:with-param name="k" select="@constrkind"/>
        <xsl:with-param name="nr" select="@constrnr"/>
        <xsl:with-param name="args" select="$argtypes"/>
        <xsl:with-param name="vis" select="Visible/Int"/>
        <xsl:with-param name="fnr" select="@formatnr"/>
        <xsl:with-param name="loci" select="$loci"/>
      </xsl:call-template>
    </xsl:element>
    <xsl:element name="b">
      <xsl:text> for </xsl:text>
    </xsl:element>
    <xsl:call-template name="pp">
      <xsl:with-param name="k" select="@constrkind"/>
      <xsl:with-param name="nr" select="@constrnr"/>
      <xsl:with-param name="args" select="$argtypes"/>
      <xsl:with-param name="pid" select="@redefnr"/>
      <xsl:with-param name="loci" select="$loci"/>
    </xsl:call-template>
    <xsl:text>;</xsl:text>
    <xsl:element name="br"/>
  </xsl:template>

  <!-- ignore forgetful functors - unhandled yet -->
  <xsl:template match="Notations/Pattern">
    <!-- pp1(#k=`@constrkind`,#nr=`@constrnr`,#vis=`Visible/Int`, -->
    <!-- #fnr=`@formatnr`, #loci="1"); <br; -->
    <xsl:if test="not(@kind = &quot;J&quot;)">
      <xsl:apply-templates select="ArgTypes"/>
      <xsl:choose>
        <xsl:when test="Expansion">
          <!-- $alc = lc(#s=`@aid`); -->
          <xsl:variable name="sym">
            <xsl:call-template name="abs1">
              <xsl:with-param name="k">
                <xsl:text>M</xsl:text>
              </xsl:with-param>
              <xsl:with-param name="fnr" select="@formatnr"/>
            </xsl:call-template>
          </xsl:variable>
          <xsl:element name="b">
            <xsl:text>mode </xsl:text>
          </xsl:element>
          <xsl:call-template name="absref">
            <xsl:with-param name="elems" select="."/>
            <xsl:with-param name="c">
              <xsl:text>0</xsl:text>
            </xsl:with-param>
            <xsl:with-param name="sym" select="$sym"/>
            <xsl:with-param name="pid" select="@relnr"/>
          </xsl:call-template>
          <!-- <a -->
          <!-- { -->
          <!-- @href=`concat($alc, ".", $ext, "#","NM",@nr)`; -->
          <!-- if [$titles="1"] { @title=`concat(@aid,":","NM",".",@nr)`; } -->
          <!-- abs1(#k = "M", #fnr = `@formatnr`); -->
          <!-- } -->
          <xsl:if test="Visible/Int">
            <xsl:text> of </xsl:text>
            <xsl:for-each select="Visible/Int">
              <xsl:call-template name="ploci">
                <xsl:with-param name="nr" select="@x"/>
              </xsl:call-template>
              <xsl:if test="not(position()=last())">
                <xsl:text>,</xsl:text>
              </xsl:if>
            </xsl:for-each>
          </xsl:if>
          <xsl:element name="b">
            <xsl:text> is </xsl:text>
          </xsl:element>
          <xsl:apply-templates select="Expansion/Typ"/>
          <xsl:text>;</xsl:text>
          <xsl:element name="br"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:variable name="loci">
            <xsl:choose>
              <xsl:when test="$mml=&quot;1&quot;">
                <xsl:text>1</xsl:text>
              </xsl:when>
              <xsl:otherwise>
                <xsl:text>2</xsl:text>
              </xsl:otherwise>
            </xsl:choose>
          </xsl:variable>
          <xsl:element name="b">
            <xsl:call-template name="mkind">
              <xsl:with-param name="kind" select="@kind"/>
            </xsl:call-template>
          </xsl:element>
          <xsl:text> </xsl:text>
          <xsl:call-template name="pp1">
            <xsl:with-param name="k" select="@constrkind"/>
            <xsl:with-param name="nr" select="@constrnr"/>
            <xsl:with-param name="vis" select="Visible/Int"/>
            <xsl:with-param name="fnr" select="@formatnr"/>
            <xsl:with-param name="loci">
              <xsl:text>1</xsl:text>
            </xsl:with-param>
          </xsl:call-template>
          <xsl:element name="br"/>
        </xsl:otherwise>
      </xsl:choose>
      <xsl:element name="br"/>
    </xsl:if>
  </xsl:template>

  <!-- ignore normal Patterns now -->
  <xsl:template match="Pattern"/>

  <!-- Default -->
  <xsl:template match="/">
    <xsl:choose>
      <xsl:when test="$generate_items = &quot;1&quot;">
        <xsl:apply-templates select="/*/JustifiedTheorem|/*/DefTheorem|/*/SchemeBlock"/>
        <xsl:apply-templates select="//RCluster|//CCluster|//FCluster|//Definition|//IdentifyWithExp"/>
        <!-- top-level lemmas -->
        <xsl:for-each select="/*/Proposition">
          <xsl:document href="proofhtml/lemma/{$anamelc}.{@propnr}" format="html"> 
          <xsl:apply-templates select="."/>
          </xsl:document> 
          <xsl:variable name="bogus" select="1"/>
        </xsl:for-each>
      </xsl:when>
      <xsl:otherwise>
        <xsl:element name="html">
          <!-- output the css defaults for div and p (for indenting) -->
          <xsl:element name="style">
            <xsl:attribute name="type">
              <xsl:text>text/css</xsl:text>
            </xsl:attribute>
            <xsl:text>
div { padding: 0 0 0 0; margin: 0 0 0 0; } 
div.add { padding-left: 3mm; padding-bottom: 0mm;  margin: 0 0 0 0; } 
p { margin: 0 0 0 0; } 
a {text-decoration:none} a:hover { color: red; } 
a.ref { font-size:x-small; }
a.ref:link { color:green; } 
a.ref:hover { color: red; } 
a.txt:link { color:black; } 
a.txt:hover { color: red; } 
span.hide { display: none; }
span.p1:hover { color : inherit; background-color : #BAFFFF; } 
span.p2:hover { color : inherit; background-color : #FFCACA; }
span.p3:hover { color : inherit; background-color : #FFFFBA; }
span.p4:hover { color : inherit; background-color : #CACAFF; }
span.p5:hover { color : inherit; background-color : #CAFFCA; }
span.p0:hover { color : inherit; background-color : #FFBAFF; }
.default { background-color: white; color: black; } 
.default:hover { background-color: white; color: black; }
</xsl:text>
          </xsl:element>
          <xsl:element name="head">
            <xsl:element name="title">
              <xsl:value-of select="$aname"/>
            </xsl:element>
            <xsl:element name="script">
              <xsl:attribute name="type">
                <xsl:text>text/javascript</xsl:text>
              </xsl:attribute>
              <xsl:text>
&lt;!-- 
function hs(obj)
{
// document.getElementById(&apos;myimage&apos;).nextSibling.style.display = &apos;block&apos;;
if (obj.nextSibling.style.display == &apos;inline&apos;)
 { obj.nextSibling.style.display = &apos;none&apos;; }
else { if (obj.nextSibling.style.display == &apos;none&apos;)
 { obj.nextSibling.style.display = &apos;inline&apos;; }
 else { obj.nextSibling.style.display = &apos;inline&apos;;  }}
return false;
}

function hs2(obj)
{
if (obj.nextSibling.style.display == &apos;block&apos;)
 { obj.nextSibling.style.display = &apos;none&apos;; }
else { if (obj.nextSibling.style.display == &apos;none&apos;)
 { obj.nextSibling.style.display = &apos;block&apos;; }
 else { obj.nextSibling.style.display = &apos;none&apos;;  }}
return false;
}
function hsNdiv(obj)
{
var ndiv = obj;
while (ndiv.nextSibling.nodeName != &apos;DIV&apos;) { ndiv = ndiv.nextSibling; }
return hs2(ndiv);
}

// explorer7 implements XMLHttpRequest in some strange way
function makeRequest(obj,url) {
        var http_request = false;
        if (window.XMLHttpRequest &amp;&amp; !(window.ActiveXObject)) { // Mozilla, Safari,...
            http_request = new XMLHttpRequest();
            if (http_request.overrideMimeType) {
                http_request.overrideMimeType(&apos;text/xml&apos;);
            }
        } else if (window.ActiveXObject) { // IE
            try {
                http_request = new ActiveXObject(&apos;Msxml2.XMLHTTP&apos;);
            } catch (e) {
                try {
                    http_request = new ActiveXObject(&apos;Microsoft.XMLHTTP&apos;);
                } catch (e) {}
            }
        }
        if (!http_request) {
            alert(&apos;Giving up :( Cannot create an XMLHTTP instance&apos;);
            return false;
        }
        http_request.onreadystatechange = function() { insertRequest(obj,http_request); };
        http_request.open(&apos;GET&apos;, url, true);
        http_request.send(null);
    }
// commented the 200 state to have local requests too
function insertRequest(obj,http_request) {
        if (http_request.readyState == 4) {
//            if (http_request.status == 200) {
	    var ndiv = obj;
	    while (ndiv.nodeName != &apos;SPAN&apos;) { ndiv = ndiv.nextSibling; }
	    ndiv.innerHTML = http_request.responseText;
	    obj.onclick = function(){ return hs2(obj) };
//            } else {
//                alert(&apos;There was a problem with the request.&apos;);
//		alert(http_request.status);
//            }
	    }}
// End --&gt;
</xsl:text>
            </xsl:element>
            <xsl:if test="$idv&gt;0">
              <xsl:element name="script">
                <xsl:attribute name="type">
                  <xsl:text>text/javascript</xsl:text>
                </xsl:attribute>
                <xsl:text>
&lt;!--
var tstp_dump;
function openSoTSTP (dump) {
var tstp_url = &apos;http://www.cs.miami.edu/~tptp/cgi-bin/SystemOnTSTP&apos;;
var tstp_browser = window.open(tstp_url, &apos;_blank&apos;);
tstp_dump = dump;
}
function getTSTPDump () {
return tstp_dump;
}
// End --&gt;
</xsl:text>
              </xsl:element>
            </xsl:if>
            <xsl:element name="base">
              <xsl:attribute name="target">
                <xsl:value-of select="$default_target"/>
              </xsl:attribute>
            </xsl:element>
          </xsl:element>
          <xsl:element name="body">
            <xsl:if test="$mk_header &gt; 0">
              <xsl:apply-templates select="document($hdr,/)/Header/*"/>
              <xsl:element name="br"/>
            </xsl:if>
            <!-- first read the keys for imported stuff -->
            <!-- apply[document($constrs,/)/Constructors/Constructor]; -->
            <!-- apply[document($thms,/)/Theorems/Theorem]; -->
            <!-- apply[document($schms,/)/Schemes/Scheme]; -->
            <!-- then process the whole document -->
            <xsl:apply-templates/>
          </xsl:element>
        </xsl:element>
      </xsl:otherwise>
    </xsl:choose>
  </xsl:template>

  <!-- tpl [*] { copy { apply [@*]; apply; } } -->
  <!-- tpl [@*] { copy-of `.`; } -->
  <!-- Header rules -->
  <xsl:template match="dc:title">
    <xsl:call-template name="pcomment">
      <xsl:with-param name="str" select="text()"/>
    </xsl:call-template>
  </xsl:template>

  <xsl:template match="dc:creator">
    <xsl:call-template name="pcomment">
      <xsl:with-param name="str" select="concat(&quot;by &quot;, text())"/>
    </xsl:call-template>
    <xsl:call-template name="pcomment">
      <xsl:with-param name="str">
        <xsl:text/>
      </xsl:with-param>
    </xsl:call-template>
  </xsl:template>

  <xsl:template match="dc:date">
    <xsl:call-template name="pcomment">
      <xsl:with-param name="str" select="concat(&quot;Received &quot;, text())"/>
    </xsl:call-template>
  </xsl:template>

  <xsl:template match="dc:rights">
    <xsl:call-template name="pcomment">
      <xsl:with-param name="str" select="concat(&quot;Copyright &quot;, text())"/>
    </xsl:call-template>
  </xsl:template>
</xsl:stylesheet>
