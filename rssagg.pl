#! /usr/bin/perl

use warnings;
use strict;
use HTTP::Status;
use LWP::UserAgent;
use Digest::MD5 'md5';
use Storable qw( retrieve nstore );
use Encode;

my $MAXITEMS = 500;
my $MAXFILES = 9;
my $MAXERRLEN = 200;
my $TITLE = 'RSSaggressor';

my $data;
my $html_fh;
my $ua = LWP::UserAgent->new;

# $ua->proxy ('http', 'http://n:7200/');
$ua->agent ($TITLE);

sub print_head {
	print $html_fh <<HTML;
<html><head>
<meta http-equiv="Content-Type" content="text/html; charset=utf-8">
<title>$TITLE</title></head><body>
<p>Generated at ${\scalar localtime}.  Older files: ${
	\join ', ', map qq|<a href="$_.html">$_</a>|, 1 .. $MAXFILES
}.</p>
<a name="a0"></a><a name="b0"></a>
HTML
}

my $ca = 1;
my $cb = 1;

sub print_foot {
	print $html_fh <<HTML
<a name="a$ca"></a><a name="b$cb"></a>
<hr><p><b>EOF.</b></p></body></html>
HTML
}

sub print_feed {
	my ($feed) = @_;

	my $err = $feed->{error} ?
		" - <font color=\"#FF0000\">$feed->{error}</font>" : '';

	if ($feed->{item} || $err) {
		if ($feed->{item}) {
			print $html_fh <<HTML;
<a name="b$cb"></a>
HTML
			$cb++;
		}
		print $html_fh <<HTML;
<hr><p><b>$feed->{line}. <a href="$feed->{link}">$feed->{title}</a></b>$err</p>
<blockquote>
HTML
		for my $item (@{ $feed->{item} }) {
			print $html_fh <<HTML;
<p>(<a name="a$ca"></a><a
href="#a@{[$ca + 1]}">v</a><a href="#a@{[$ca - 1]}">^</a><a
href="#b$cb">V</a>) <a href="$item->{link}">$item->{title}</a></p>
<blockquote><p>$item->{text}</p></blockquote>
HTML
			$ca++;
		}
		print $html_fh <<HTML;
</blockquote>
HTML
	}
}

# html

my @tag_single = qw( br hr img );
my @tag_double = qw(
	a b blockquote code em i li ol p pre
	strike strong table td tr tt ul	font
);
my %tag = ((map { $_ => 1 } @tag_single), map { $_ => 2 } @tag_double);

sub html_sane {	# an oxymoron
	my ($res) = @_;

	my @stack;
	$res =~ s/<!--.*?-->//sg;
	$res =~ s/<!--.*/<i>broken html comment was here<\/i>/s;
	$res =~ s^<\s*(/?)(\w*)(.*?)(?:>|\z)^
		my ($close, $tag, $rest) = ($1, lc $2, $3);
		my $res = '';
		if ($tag{$tag} && !$close) {
			push @stack, $tag if $tag{$tag} == 2;
			$rest .= '"' if $rest =~ y/"// & 1; # XXX
			$res = "<$tag$rest>";
		} elsif ($tag{$tag} && $close) {
			if ($tag{$tag} == 2) {
				1 while @stack and
					$res .= "</$stack[-1]>",
					$tag ne pop @stack;
			} else {
				$res .= "</$tag>";
			}
		}
		$res
	^seg;
	$res .= "</${\pop @stack}>" while @stack;
	$res
}

sub html_esc {
	my ($str) = @_;

	s/&/&amp;/g, s/</&lt;/g, s/>/&gt;/g, s/"/&quot;/g for $str;
	return $str;
}

# xml

sub xml_tag {
	my ($ref, $tag) = @_;

	$$ref =~ s# < $tag \b [^>]* > (.*?) </ $tag \b [^>]* > ##six ?
		$1 : undef;
}

sub xml_must {
	my ($ref, $tag) = @_;

	my $res = xml_tag ($ref, $tag);
	die "no tag $tag" if !defined $res;
	return $res;
}

sub xml_link_href {
	my ($ref) = @_;

	$$ref =~ m# < link \b [^>]* \b href="([^"]*)" #six ? $1 :
	$$ref =~ m# < link \b [^>]* \b href='([^']*)' #six ? $1 :
		undef;
}

my %entity = (
	lt	=> '<',
	gt	=> '>',
	amp	=> '&',
	quot	=> '"',
	apos	=> "'",
);

sub xml_decode {
	my ($txt) = @_;

	$txt =~ s/ <!\[CDATA\[ (((?!]]>).)*) ]]> /$1/xsg;

	$txt =~ s/&([a-z]+);/ $entity{$1} || $& /eg if $txt !~ /[<>]/;
	$txt =~ s/&#([0-9]+);/ chr $1 /eg;

	return $txt;
}

sub text_sane {
	my ($txt) = @_;

	html_sane (xml_decode ($txt))
}

sub text_notag {
	my ($txt) = @_;

	$txt = text_sane ($txt);
	$txt =~ s/<.*?>//g;
	$txt
}

# item[]/(title/link/description)

sub parse_items {
	my ($ref, $tag) = @_;

	my @item;
	while (my $item = xml_tag ($ref, $tag || 'item')) {
		my %item;
		$item{link}  = text_notag (
			xml_tag (\$item, 'guid') ||
			xml_link_href (\$item) ||
			xml_must (\$item, 'link')
		);
		$item{title} = text_notag (
			xml_tag (\$item, 'title') ||
			$item{link}
		);
		$item{text}  = text_sane (
			xml_tag (\$item, 'content') ||
			xml_tag (\$item, 'description') ||
			xml_tag (\$item, 'summary') ||
			$item{title}
		);
		push @item, \%item;
	}
	return scalar \@item;
}

# rss/channel/(title|link|item[])

sub parse_rss {
        my ($xml) = @_;

	my $rss = xml_must (\$xml, 'rss');
	my $chan = xml_must (\$rss, 'channel');
	my $items = parse_items (\$chan);
	return {
		title	=> xml_must (\$chan, 'title'),
		link	=> xml_must (\$chan, 'link'),
		item	=> $items,
	};
}

# rdf/(channel/(title|link)|item[])

sub parse_rdf {
        my ($xml) = @_;

	my $rdf = xml_must (\$xml, 'rdf:RDF');
	my $chan = xml_must (\$rdf, 'channel');
	return {
		title	=> xml_must (\$chan, 'title'),
		link	=> xml_must (\$chan, 'link'),
		item	=> parse_items (\$rdf),
	};
}

# feed/(channel/?(title|link))|entry[])

sub parse_atom {
        my ($xml) = @_;

	my $feed = xml_must (\$xml, 'feed');
	my $chan = xml_tag (\$feed, 'channel') || $feed;
	my $link = xml_link_href (\$chan) || xml_must (\$chan, 'link');
	return {
		title	=> xml_must (\$chan, 'title'),
		link	=> $link,
		item	=> parse_items (\$feed, 'entry'),
	};
}

sub parse {
	my ($txt) = @_;

	# XXX gzip

	if ($txt =~
		/<\?xml \b [^?>]* \b encoding=("|')([^'"]+)\1 [^?>]* \?>/six) {
		eval { $txt = decode ($2, $txt); };
	}
	# XXX else BOM

	my $res =
		eval { parse_rss ($txt) } ||
		eval { parse_rdf ($txt) } ||
		eval { parse_atom ($txt) } ||
		{ error => html_esc (substr "$@ $txt", 0, $MAXERRLEN) };

	$res->{$_} = text_notag ($res->{$_} || '') for qw( title link );

	return $res;
}

sub letters {
	my ($str) = @_;

	$str =~ s/<.*?>//sg;
	$str =~ y/\0-@[-`{-~//d;
	encode ('utf-8', $str);
}

sub parse_feed {
	my ($feed, $xml) = @_;

	my $parse = parse ($xml);

	defined $parse->{$_} and $feed->{$_} = $parse->{$_}
		for qw( title link error );

	my $md5s = $feed->{data}{md5} ||= [];
	my %md5; @md5{ @$md5s } = ();
	for my $i (@{ $parse->{item} }) {
		my $md5 = md5 (letters ($i->{text}) || $i->{link});
		next if exists $md5{$md5};
		$md5{$md5}++;
		push @{ $feed->{item} }, $i;
		unshift @$md5s, $md5;
	}
	$#$md5s = $MAXITEMS if $#$md5s > $MAXITEMS;
}

sub get_feed {
	my ($feed) = @_;

	my @hdr;
	push @hdr, if_modified_since => $feed->{data}{date}
		if $feed->{data}{date};
	push @hdr, if_none_match => $feed->{data}{etag}
		if $feed->{data}{etag};

	my $res = eval {
		local $SIG{ALRM} = sub { die 'timeout' };
		alarm 10;
		$ua->get ($feed->{url}, @hdr);
	};
	if ($@) {
		die $@ if $@ !~ /^timeout/;
		$res ||= HTTP::Response->new (500, 'Timeout');
	}
	alarm 0;

	$|++, print "." if -t;

	if ($res->code == RC_OK) {
		my $xml = $res->content;
		parse_feed ($feed, $xml);
		if (!$feed->{error}) {
			my $hdr = $res->headers;
			$feed->{data}{date} = $hdr->header ('Last-modified');
			$feed->{data}{etag} = $hdr->header ('ETag');
			unlink "xml/$feed->{line}";
		} elsif (-d 'xml') {
			open my $f, "> xml/$feed->{line}" or die "open: $!";
			binmode $f;
			print $f $xml;
			close $f or die "close: $!";
		}
	} elsif ($res->code != RC_NOT_MODIFIED) {
		$feed->{error} = 'http: ' . $res->status_line;
	}
	$feed->{title} ||= $feed->{link} ||= $feed->{url};
}

sub process_list {
	open my $f, 'rss.list' or die "open rss.list: $!";
	my %urls;
	print_head ();
	my $line;
	for my $url (map /(\S+)/, <$f>) {
		$line++;
		warn ("rss.list: duplicated entry $url\n"), next
			if $urls{$url}++;
		my $feed = {
			url	=> $url,
			line	=> $line,
			data	=> ($data->{$url} ||= {}),
		};
		get_feed ($feed);
		print_feed ($feed);
	}
	print_foot ();
	exists $urls{$_} || delete $data->{$_} for keys %$data;
}

die "usage: $0 <dir>\n" if @ARGV != 1;
chdir $ARGV[0] or die "chdir @ARGV: $!";

my $TMP = 'index.html.tmp';

die "$TMP already exists" if -f $TMP;

$data = eval { retrieve ('rss.data') };
warn "no data found: error '$@' - will use empty\n" if $@;

open $html_fh, '>:utf8', $TMP or die "open $TMP: $!";
my $prev = select $html_fh; $|++; select $prev;

process_list ();

close $html_fh or die;

nstore $data, 'rss.data.tmp';
rename 'rss.data.tmp', 'rss.data' or die "rename rss.data.tmp: $!";

rename "$_.html", ($_ + 1) . '.html' for reverse 1 .. $MAXFILES - 1;
rename 'index.html', '1.html';
rename $TMP, 'index.html' or die "rename $TMP: $!";
