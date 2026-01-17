/*
 * OSCam WebIf Wiki generator
 * Parses Wiki markdown files and generates C code with help texts
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 */
#include <ctype.h>
#include <stdio.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <errno.h>
#include <dirent.h>

#include "../config.h"
#ifdef WITH_COMPRESS_WEBIF
#include "../minilzo/minilzo.h"
#define USE_COMPRESSION 1
#endif

#define MAX_WIKI_ENTRIES 1024
#define MAX_PARAM_LEN 64
#define MAX_CONFIG_LEN 32
#define MAX_SECTION_LEN 32
#define MAX_TEXT_LEN 4096
#define MAX_LINE_LEN 1024
#define MAX_FLAG_LEN 64

/* is_defined.txt content - loaded at runtime */
static char *is_defined_content = NULL;
static size_t is_defined_len = 0;

/* Safe string copy - always null-terminates */
static void safe_strncpy(char *dst, const char *src, size_t size)
{
	if(size == 0)
		{ return; }
	size_t i;
	for(i = 0; i < size - 1 && src[i] != '\0'; i++)
	{
		dst[i] = src[i];
	}
	dst[i] = '\0';
}

static char *wiki_dir = "../wiki/pages/configuration";
static char *is_defined_file = "is_defined.txt";
static char *output_wiki_c = "pages_wiki.c";
static char *output_wiki_h = "pages_wiki.h";

struct wiki_entry
{
	char param[MAX_PARAM_LEN];      /* parameter name, e.g. "serverip" */
	char config[MAX_CONFIG_LEN];    /* config file, e.g. "conf", "server", "user" */
	char section[MAX_SECTION_LEN];  /* section name, e.g. "dvbapi", "anticasc" */
	char text[MAX_TEXT_LEN];        /* help text */
	int text_len;
	int8_t status;                  /* 0=ok, 1=review, 2=missing */
#ifdef USE_COMPRESSION
	uint32_t param_ofs;
	uint32_t config_ofs;
	uint32_t section_ofs;
	uint32_t text_ofs;
#endif
};

struct wiki_data
{
	unsigned int num;
	struct wiki_entry entries[MAX_WIKI_ENTRIES];
};

static struct wiki_data wiki;
static FILE *output_file;

/* Statistics */
static unsigned int stats_total = 0;
static unsigned int stats_included = 0;
static unsigned int stats_skipped = 0;

__attribute__ ((noreturn)) static void die(const char *s, ...)
{
	va_list args;
	va_start(args, s);
	fprintf(stderr, "ERROR: ");
	vfprintf(stderr, s, args);
	if(s[strlen(s) - 1] != '\n')
		{ fprintf(stderr, "\n"); }
	va_end(args);
	exit(EXIT_FAILURE);
}

static FILE *xfopen(char *filename, char *mode)
{
	FILE *fh = fopen(filename, mode);
	if(!fh)
		{ die("fopen(%s, %s): %s\n", filename, mode, strerror(errno)); }
	return fh;
}

/* Read file into memory */
static void readfile(const char *filename, char **data, size_t *data_len)
{
	FILE *f = fopen(filename, "rb");
	if(!f)
	{
		*data = NULL;
		*data_len = 0;
		return;
	}

	fseek(f, 0, SEEK_END);
	*data_len = ftell(f);
	fseek(f, 0, SEEK_SET);

	*data = malloc(*data_len + 1);
	if(!*data)
	{
		fclose(f);
		*data_len = 0;
		return;
	}

	if(fread(*data, 1, *data_len, f) != *data_len)
	{
		free(*data);
		*data = NULL;
		*data_len = 0;
		fclose(f);
		return;
	}

	(*data)[*data_len] = '\0';
	fclose(f);
}

/* Check if a flag is defined in is_defined.txt */
static bool is_flag_defined(const char *flag)
{
	if(!is_defined_content || !flag || !flag[0])
		{ return false; }

	/* Search for flag as whole word (line by line) */
	const char *p = is_defined_content;
	size_t flag_len = strlen(flag);

	while(*p)
	{
		/* Skip leading whitespace */
		while(*p && isspace((unsigned char)*p))
			{ p++; }

		if(!*p)
			{ break; }

		/* Find end of line */
		const char *line_start = p;
		while(*p && *p != '\n' && *p != '\r')
			{ p++; }

		size_t line_len = p - line_start;

		/* Compare (trimmed) */
		while(line_len > 0 && isspace((unsigned char)line_start[line_len - 1]))
			{ line_len--; }

		if(line_len == flag_len && strncmp(line_start, flag, flag_len) == 0)
			{ return true; }

		/* Skip newline */
		while(*p && (*p == '\n' || *p == '\r'))
			{ p++; }
	}

	return false;
}

/* Check if entry should be included based on flag and is_defined.txt */
static bool should_include_entry(const char *flag)
{
	/* No flag = always include */
	if(!flag || !flag[0])
		{ return true; }

	/* No is_defined.txt = include all (no filtering) */
	if(!is_defined_content)
		{ return true; }

	/* Check if flag is defined */
	return is_flag_defined(flag);
}

/* Extract config name from filename, e.g. "oscam.conf.md" -> "conf" */
static void extract_config_name(const char *filename, char *config, size_t config_size)
{
	const char *base = filename;
	const char *slash = strrchr(filename, '/');
	if(slash)
		{ base = slash + 1; }

	/* Skip "oscam." prefix */
	if(strncmp(base, "oscam.", 6) == 0)
		{ base += 6; }

	/* Copy until ".md" */
	size_t i = 0;
	while(*base && *base != '.' && i < config_size - 1)
	{
		config[i++] = *base++;
	}
	config[i] = '\0';
}

/* Trim whitespace from both ends of string */
static char *trim(char *str)
{
	char *end;

	/* Trim leading space */
	while(isspace((unsigned char)*str))
		{ str++; }

	if(*str == 0)
		{ return str; }

	/* Trim trailing space */
	end = str + strlen(str) - 1;
	while(end > str && isspace((unsigned char)*end))
		{ end--; }

	end[1] = '\0';
	return str;
}

/* Escape string for C string literal */
static void escape_for_c(const char *src, char *dst, size_t dst_size)
{
	size_t j = 0;
	for(size_t i = 0; src[i] && j < dst_size - 2; i++)
	{
		switch(src[i])
		{
		case '\n':
			if(j < dst_size - 3) { dst[j++] = '\\'; dst[j++] = 'n'; }
			break;
		case '\r':
			/* Skip CR */
			break;
		case '\t':
			if(j < dst_size - 3) { dst[j++] = '\\'; dst[j++] = 't'; }
			break;
		case '\\':
			if(j < dst_size - 3) { dst[j++] = '\\'; dst[j++] = '\\'; }
			break;
		case '"':
			if(j < dst_size - 3) { dst[j++] = '\\'; dst[j++] = '"'; }
			break;
		default:
			dst[j++] = src[i];
			break;
		}
	}
	dst[j] = '\0';
}

/*
 * Check if line is a parameter heading (### param_name)
 * Returns true if it's a parameter heading, extracts param_name
 */
static bool is_param_heading(const char *line, char *param_name, size_t param_size)
{
	param_name[0] = '\0';

	/* Skip leading whitespace */
	while(isspace((unsigned char)*line))
		{ line++; }

	/* Check for ### */
	if(strncmp(line, "###", 3) != 0)
		{ return false; }

	line += 3;

	/* Skip whitespace after ### */
	while(isspace((unsigned char)*line))
		{ line++; }

	/* Extract parameter name (alphanumeric and underscore) */
	size_t i = 0;
	while((isalnum((unsigned char)*line) || *line == '_' || *line == '-') && i < param_size - 1)
	{
		param_name[i++] = *line++;
	}
	param_name[i] = '\0';

	if(i == 0)
		{ return false; }

	return true;
}

/*
 * Extract flag from text if it contains "**(requires `FLAG` compilation flag)**"
 * Returns true if flag was found, extracts the flag name
 */
static bool extract_flag_from_text(const char *text, char *flag, size_t flag_size)
{
	flag[0] = '\0';

	/* Search for "(requires `" pattern */
	const char *pattern = "(requires `";
	const char *p = strstr(text, pattern);
	if(!p)
		{ return false; }

	p += strlen(pattern);

	/* Extract flag name until closing backtick */
	size_t i = 0;
	while(*p && *p != '`' && i < flag_size - 1)
	{
		flag[i++] = *p++;
	}
	flag[i] = '\0';

	return (i > 0 && *p == '`');
}

/*
 * Determine documentation status from text content
 * Returns: 0=ok, 1=review, 2=missing
 */
static int8_t get_doc_status(const char *text)
{
	if(strstr(text, "NEEDS REVIEW"))
		{ return 1; }
	if(strstr(text, "MISSING DOCUMENTATION") || strstr(text, "Missing documentation"))
		{ return 2; }
	return 0;
}

/* Check if line is a section separator (---) */
static bool is_separator(const char *line)
{
	/* Skip leading whitespace */
	while(isspace((unsigned char)*line))
		{ line++; }

	/* Check for --- (at least 3 dashes) */
	int dashes = 0;
	while(*line == '-')
	{
		dashes++;
		line++;
	}

	/* Rest should be whitespace or end of line */
	while(*line)
	{
		if(!isspace((unsigned char)*line))
			{ return false; }
		line++;
	}

	return dashes >= 3;
}

/* Check if line is a section heading (## [section] Section) - not parameter
 * If it is, extract the section name (e.g. "dvbapi" from "## [dvbapi] Section")
 * Returns true if it's a section heading
 */
static bool is_section_heading(const char *line, char *section_name, size_t section_size)
{
	if(section_name && section_size > 0)
		{ section_name[0] = '\0'; }

	/* Skip leading whitespace */
	while(isspace((unsigned char)*line))
		{ line++; }

	/* ## but not ### */
	if(!(line[0] == '#' && line[1] == '#' && line[2] != '#'))
		{ return false; }

	/* Skip ## and whitespace */
	line += 2;
	while(isspace((unsigned char)*line))
		{ line++; }

	/* Check for [section] pattern */
	if(*line == '[' && section_name && section_size > 0)
	{
		line++;
		size_t i = 0;
		while(*line && *line != ']' && i < section_size - 1)
		{
			section_name[i++] = *line++;
		}
		section_name[i] = '\0';
	}

	return true;
}

/* Add wiki entry if it should be included */
static void add_wiki_entry(const char *param, const char *config, const char *section, const char *text)
{
	char flag[MAX_FLAG_LEN];

	stats_total++;

	/* Extract flag from text content */
	extract_flag_from_text(text, flag, sizeof(flag));

	if(!should_include_entry(flag))
	{
		stats_skipped++;
		return;
	}

	if(wiki.num >= MAX_WIKI_ENTRIES)
	{
		fprintf(stderr, "Warning: Too many wiki entries, skipping %s.%s.%s\n", config, section, param);
		return;
	}

	struct wiki_entry *e = &wiki.entries[wiki.num];
	safe_strncpy(e->param, param, MAX_PARAM_LEN);
	safe_strncpy(e->config, config, MAX_CONFIG_LEN);
	safe_strncpy(e->section, section ? section : "", MAX_SECTION_LEN);
	e->status = get_doc_status(text);

	char *text_copy = strdup(text);
	if(text_copy)
	{
		char *trimmed = trim(text_copy);
		escape_for_c(trimmed, e->text, MAX_TEXT_LEN);
		free(text_copy);
	}
	else
	{
		e->text[0] = '\0';
	}

	e->text_len = strlen(e->text);
	wiki.num++;
	stats_included++;
}

/* Parse a single markdown file */
static void parse_wiki_file(const char *filepath)
{
	FILE *f = fopen(filepath, "r");
	if(!f)
	{
		fprintf(stderr, "Warning: Cannot open %s: %s\n", filepath, strerror(errno));
		return;
	}

	char config[MAX_CONFIG_LEN];
	extract_config_name(filepath, config, sizeof(config));

	char line[MAX_LINE_LEN];
	char current_param[MAX_PARAM_LEN] = "";
	char current_section[MAX_SECTION_LEN] = "";
	char current_text[MAX_TEXT_LEN] = "";
	int text_pos = 0;
	bool in_param = false;

	while(fgets(line, sizeof(line), f))
	{
		char param_name[MAX_PARAM_LEN];
		char section_name[MAX_SECTION_LEN];

		if(is_param_heading(line, param_name, sizeof(param_name)))
		{
			/* Save previous parameter if exists */
			if(in_param && current_param[0] && text_pos > 0)
			{
				current_text[text_pos] = '\0';
				add_wiki_entry(current_param, config, current_section, current_text);
			}

			/* Start new parameter */
			safe_strncpy(current_param, param_name, MAX_PARAM_LEN);
			text_pos = 0;
			current_text[0] = '\0';
			in_param = true;
		}
		else if(is_section_heading(line, section_name, sizeof(section_name)))
		{
			/* Save current parameter before section change */
			if(in_param && current_param[0] && text_pos > 0)
			{
				current_text[text_pos] = '\0';
				add_wiki_entry(current_param, config, current_section, current_text);
			}
			in_param = false;
			current_param[0] = '\0';
			text_pos = 0;

			/* Update current section if extracted */
			if(section_name[0])
			{
				safe_strncpy(current_section, section_name, MAX_SECTION_LEN);
			}
		}
		else if(in_param)
		{
			/* Check for end of parameter section (separator) */
			if(is_separator(line))
			{
				/* Save current parameter */
				if(current_param[0] && text_pos > 0)
				{
					current_text[text_pos] = '\0';
					add_wiki_entry(current_param, config, current_section, current_text);
				}
				in_param = false;
				current_param[0] = '\0';
				text_pos = 0;
			}
			else
			{
				/* Append line to current text */
				int line_len = strlen(line);
				if(text_pos + line_len < MAX_TEXT_LEN - 1)
				{
					memcpy(current_text + text_pos, line, line_len);
					text_pos += line_len;
				}
			}
		}
	}

	/* Save last parameter if file ends without separator */
	if(in_param && current_param[0] && text_pos > 0)
	{
		current_text[text_pos] = '\0';
		add_wiki_entry(current_param, config, current_section, current_text);
	}

	fclose(f);
}

/* Scan wiki directory for markdown files */
static void scan_wiki_directory(const char *dirpath)
{
	DIR *dir = opendir(dirpath);
	if(!dir)
	{
		fprintf(stderr, "Warning: Cannot open wiki directory %s: %s\n", dirpath, strerror(errno));
		return;
	}

	unsigned int file_count = 0;
	struct dirent *entry;
	while((entry = readdir(dir)) != NULL)
	{
		/* Skip hidden files and directories */
		if(entry->d_name[0] == '.')
			{ continue; }

		/* Check for .md extension */
		size_t len = strlen(entry->d_name);
		if(len < 4 || strcmp(entry->d_name + len - 3, ".md") != 0)
			{ continue; }

		/* Build full path */
		char filepath[512];
		snprintf(filepath, sizeof(filepath), "%s/%s", dirpath, entry->d_name);

		parse_wiki_file(filepath);
		file_count++;
	}

	closedir(dir);

	printf("WIKI\tParsed %u markdown files in %s\n", file_count, dirpath);
}

/* Generate pages_wiki.h */
static void generate_header(void)
{
	output_file = xfopen(output_wiki_h, "w");

	fprintf(output_file, "/*\n");
	fprintf(output_file, " * OSCam WebIf Wiki data - AUTO GENERATED, DO NOT EDIT!\n");
	fprintf(output_file, " * Generated by wiki_gen from wiki markdown files\n");
	fprintf(output_file, " */\n");
	fprintf(output_file, "#ifndef WEBIF_PAGES_WIKI_H_\n");
	fprintf(output_file, "#define WEBIF_PAGES_WIKI_H_\n");
	fprintf(output_file, "\n");
	fprintf(output_file, "#ifdef WEBIF_WIKI\n");
	fprintf(output_file, "\n");
#ifdef USE_COMPRESSION
	fprintf(output_file, "#define COMPRESSED_WIKI 1\n\n");
	fprintf(output_file, "struct wiki_entry {\n");
	fprintf(output_file, "\tuint32_t param_ofs;\n");
	fprintf(output_file, "\tuint32_t config_ofs;\n");
	fprintf(output_file, "\tuint32_t section_ofs;\n");
	fprintf(output_file, "\tuint32_t text_ofs;\n");
	fprintf(output_file, "\tint8_t status;\n");
	fprintf(output_file, "};\n");
	fprintf(output_file, "\n");
	fprintf(output_file, "int32_t wiki_count(void);\n");
	fprintf(output_file, "const struct wiki_entry *wiki_get_entries(void);\n");
	fprintf(output_file, "const char *wiki_get_help(const char *config, const char *section, const char *param);\n");
	fprintf(output_file, "int8_t wiki_get_status(const char *config, const char *section, const char *param);\n");
	fprintf(output_file, "void wiki_get_data(const char **data, size_t *data_len, size_t *data_olen);\n");
	fprintf(output_file, "char *wiki_get_decompressed_data(void);\n");
	fprintf(output_file, "void webif_wiki_prepare(void);\n");
	fprintf(output_file, "void webif_wiki_free(void);\n");
#else
	fprintf(output_file, "struct wiki_entry {\n");
	fprintf(output_file, "\tconst char *param;\n");
	fprintf(output_file, "\tconst char *config;\n");
	fprintf(output_file, "\tconst char *section;\n");
	fprintf(output_file, "\tconst char *text;\n");
	fprintf(output_file, "\tint8_t status;\n");
	fprintf(output_file, "};\n");
	fprintf(output_file, "\n");
	fprintf(output_file, "int32_t wiki_count(void);\n");
	fprintf(output_file, "const struct wiki_entry *wiki_get_entries(void);\n");
	fprintf(output_file, "const char *wiki_get_help(const char *config, const char *section, const char *param);\n");
	fprintf(output_file, "int8_t wiki_get_status(const char *config, const char *section, const char *param);\n");
	fprintf(output_file, "void webif_wiki_prepare(void);\n");
	fprintf(output_file, "void webif_wiki_free(void);\n");
#endif
	fprintf(output_file, "\n");
	fprintf(output_file, "#endif /* WEBIF_WIKI */\n");
	fprintf(output_file, "\n");
	fprintf(output_file, "#endif /* WEBIF_PAGES_WIKI_H_ */\n");

	fclose(output_file);
}

#ifdef USE_COMPRESSION
#define HEAP_ALLOC(var, size) \
	lzo_align_t __LZO_MMODEL var [ ((size) + (sizeof(lzo_align_t) - 1)) / sizeof(lzo_align_t) ]

static HEAP_ALLOC(wrkmem, LZO1X_1_MEM_COMPRESS);

static void dump_cbinary(char *var_name, uint8_t *buf, size_t buf_len, size_t obuf_len)
{
	fprintf(output_file, "static const char   *%s     = \"", var_name);
	size_t i;
	for(i = 0; i < buf_len; i++)
	{
		fprintf(output_file, "\\x%02x", buf[i]);
	}
	fprintf(output_file, "\";\n");
	fprintf(output_file, "static const size_t %s_len  = %zu;\n"  , var_name, buf_len);
	fprintf(output_file, "static const size_t %s_olen = %zu;\n\n", var_name, obuf_len);
}
#endif

/* Generate pages_wiki.c */
static void generate_source(void)
{
	unsigned int i;

	output_file = xfopen(output_wiki_c, "w");

	fprintf(output_file, "/*\n");
	fprintf(output_file, " * OSCam WebIf Wiki data - AUTO GENERATED, DO NOT EDIT!\n");
	fprintf(output_file, " * Generated by wiki_gen from wiki markdown files\n");
	fprintf(output_file, " */\n");
	fprintf(output_file, "#define MODULE_LOG_PREFIX \"webif\"\n");
	fprintf(output_file, "#include \"../globals.h\"\n");
	fprintf(output_file, "\n");
	fprintf(output_file, "#if defined(WEBIF) && defined(WEBIF_WIKI)\n");
	fprintf(output_file, "\n");
	fprintf(output_file, "#include \"pages_wiki.h\"\n");
	fprintf(output_file, "#include <string.h>\n");
#ifdef USE_COMPRESSION
	fprintf(output_file, "#ifdef WITH_COMPRESS_WEBIF\n");
	fprintf(output_file, "#include \"../minilzo/minilzo.h\"\n");
	fprintf(output_file, "#endif\n");
#endif
	fprintf(output_file, "\n");

#ifdef USE_COMPRESSION
	/* Calculate positions */
	uint32_t cur_pos = 0;
#define align_up(val, align) (val += (align - val % align))
	for(i = 0; i < wiki.num; i++)
	{
		struct wiki_entry *e = &wiki.entries[i];
		e->param_ofs = cur_pos;
		cur_pos += strlen(e->param) + 1;
		align_up(cur_pos, sizeof(void *));
		e->config_ofs = cur_pos;
		cur_pos += strlen(e->config) + 1;
		align_up(cur_pos, sizeof(void *));
		e->section_ofs = cur_pos;
		cur_pos += strlen(e->section) + 1;
		align_up(cur_pos, sizeof(void *));
		e->text_ofs = cur_pos;
		cur_pos += strlen(e->text) + 1;
		align_up(cur_pos, sizeof(void *));
	}

	/* Allocate and populate data buffer */
	uint32_t data_len = cur_pos;
	if(!data_len)
		{ die("No wiki entries"); }
	uint8_t *data = calloc(1, data_len);
	if(!data)
		{ die("Can't alloc %u bytes", data_len); }
	for(i = 0; i < wiki.num; i++)
	{
		struct wiki_entry *e = &wiki.entries[i];
		memcpy(data + e->param_ofs, e->param, strlen(e->param));
		memcpy(data + e->config_ofs, e->config, strlen(e->config));
		memcpy(data + e->section_ofs, e->section, strlen(e->section));
		memcpy(data + e->text_ofs, e->text, strlen(e->text));
	}

	/* Compress data */
	lzo_uint in_len = data_len;
	lzo_uint out_len = data_len + data_len / 16 + 64 + 3;
	uint8_t *out = malloc(out_len);
	if(!out)
		{ die("Can't alloc %zu bytes", out_len); }

	if(lzo_init() != LZO_E_OK)
	{
		fprintf(stderr, "internal error - lzo_init() failed!\n");
		free(out);
		free(data);
		exit(3);
	}

	int r = lzo1x_1_compress(data, in_len, out, &out_len, wrkmem);
	if(r == LZO_E_OK)
	{
		printf("GEN\tCompressed %lu wiki entry bytes into %lu bytes. %ld saved bytes (%.1f%%).\n",
				(unsigned long)in_len, (unsigned long)out_len,
				(long)in_len - (long)out_len, 100.0 - ((float)out_len / in_len) * 100);
	}
	else
	{
		fprintf(stderr, "compression failed: %d\n", r);
		free(out);
		free(data);
		exit(2);
	}

	dump_cbinary("wiki_data", out, out_len, data_len);
	free(out);
	free(data);
#endif

	/* Generate wiki entries array - all entries are unconditional (filtering done at gen time) */
	fprintf(output_file, "static const struct wiki_entry wiki_entries[] = {\n");
	for(i = 0; i < wiki.num; i++)
	{
		struct wiki_entry *e = &wiki.entries[i];
#ifdef USE_COMPRESSION
		fprintf(output_file, "\t{ .param_ofs=%5u, .config_ofs=%5u, .section_ofs=%5u, .text_ofs=%5u, .status=%d }, /* %s.%s.%s */\n",
				e->param_ofs, e->config_ofs, e->section_ofs, e->text_ofs, e->status, e->config, e->section, e->param);
#else
		fprintf(output_file, "\t{ .param = \"%s\", .config = \"%s\", .section = \"%s\", .text = \"%s\", .status = %d },\n",
				e->param, e->config, e->section, e->text, e->status);
#endif
	}
	fprintf(output_file, "};\n");
	fprintf(output_file, "\n");

	/* Generate accessor functions */
	fprintf(output_file, "int32_t wiki_count(void)\n");
	fprintf(output_file, "{\n");
	fprintf(output_file, "\treturn sizeof(wiki_entries) / sizeof(struct wiki_entry);\n");
	fprintf(output_file, "}\n");
	fprintf(output_file, "\n");

	fprintf(output_file, "const struct wiki_entry *wiki_get_entries(void)\n");
	fprintf(output_file, "{\n");
	fprintf(output_file, "\treturn wiki_entries;\n");
	fprintf(output_file, "}\n");
	fprintf(output_file, "\n");

#ifdef USE_COMPRESSION
	fprintf(output_file, "static char *wiki_data_decompressed = NULL;\n");
	fprintf(output_file, "\n");

	fprintf(output_file, "void wiki_get_data(const char **data, size_t *data_len, size_t *data_olen)\n");
	fprintf(output_file, "{\n");
	fprintf(output_file, "\t*data = wiki_data;\n");
	fprintf(output_file, "\t*data_len = wiki_data_len;\n");
	fprintf(output_file, "\t*data_olen = wiki_data_olen;\n");
	fprintf(output_file, "}\n");
	fprintf(output_file, "\n");

	fprintf(output_file, "void webif_wiki_prepare(void)\n");
	fprintf(output_file, "{\n");
	fprintf(output_file, "\tif(wiki_data_decompressed) return;\n");
	fprintf(output_file, "\tconst char *data;\n");
	fprintf(output_file, "\tsize_t data_len, data_olen;\n");
	fprintf(output_file, "\twiki_get_data(&data, &data_len, &data_olen);\n");
	fprintf(output_file, "\twiki_data_decompressed = malloc(data_olen);\n");
	fprintf(output_file, "\tif(!wiki_data_decompressed)\n");
	fprintf(output_file, "\t{\n");
	fprintf(output_file, "\t\tcs_log(\"wiki: cannot allocate %%zu bytes for decompression\", data_olen);\n");
	fprintf(output_file, "\t\treturn;\n");
	fprintf(output_file, "\t}\n");
	fprintf(output_file, "\tlzo_uint new_len = data_olen;\n");
	fprintf(output_file, "\tint r = lzo1x_decompress_safe((uint8_t *)data, data_len, (uint8_t *)wiki_data_decompressed, &new_len, NULL);\n");
	fprintf(output_file, "\tif(r == LZO_E_OK && new_len == data_olen)\n");
	fprintf(output_file, "\t{\n");
	fprintf(output_file, "\t\tcs_log(\"wiki: decompressed %%zu bytes back into %%zu bytes\", data_len, data_olen);\n");
	fprintf(output_file, "\t}\n");
	fprintf(output_file, "\telse\n");
	fprintf(output_file, "\t{\n");
	fprintf(output_file, "\t\tcs_log(\"wiki: decompression failed: %%d\", r);\n");
	fprintf(output_file, "\t\tfree(wiki_data_decompressed);\n");
	fprintf(output_file, "\t\twiki_data_decompressed = NULL;\n");
	fprintf(output_file, "\t}\n");
	fprintf(output_file, "}\n");
	fprintf(output_file, "\n");

	fprintf(output_file, "void webif_wiki_free(void)\n");
	fprintf(output_file, "{\n");
	fprintf(output_file, "\tif(wiki_data_decompressed)\n");
	fprintf(output_file, "\t{\n");
	fprintf(output_file, "\t\tfree(wiki_data_decompressed);\n");
	fprintf(output_file, "\t\twiki_data_decompressed = NULL;\n");
	fprintf(output_file, "\t}\n");
	fprintf(output_file, "}\n");
	fprintf(output_file, "\n");

	fprintf(output_file, "char *wiki_get_decompressed_data(void)\n");
	fprintf(output_file, "{\n");
	fprintf(output_file, "\treturn wiki_data_decompressed;\n");
	fprintf(output_file, "}\n");
	fprintf(output_file, "\n");

	fprintf(output_file, "const char *wiki_get_help(const char *config, const char *section, const char *param)\n");
	fprintf(output_file, "{\n");
	fprintf(output_file, "\tif(!wiki_data_decompressed) return NULL;\n");
	fprintf(output_file, "\tint32_t i, count = wiki_count();\n");
	fprintf(output_file, "\tconst char *fallback = NULL;\n");
	fprintf(output_file, "\tfor(i = 0; i < count; i++)\n");
	fprintf(output_file, "\t{\n");
	fprintf(output_file, "\t\tconst char *e_config = wiki_data_decompressed + wiki_entries[i].config_ofs;\n");
	fprintf(output_file, "\t\tconst char *e_section = wiki_data_decompressed + wiki_entries[i].section_ofs;\n");
	fprintf(output_file, "\t\tconst char *e_param = wiki_data_decompressed + wiki_entries[i].param_ofs;\n");
	fprintf(output_file, "\t\tif(strcmp(e_config, config) == 0 && strcmp(e_param, param) == 0)\n");
	fprintf(output_file, "\t\t{\n");
	fprintf(output_file, "\t\t\tif(section && section[0] && strcmp(e_section, section) == 0)\n");
	fprintf(output_file, "\t\t\t\treturn wiki_data_decompressed + wiki_entries[i].text_ofs;\n");
	fprintf(output_file, "\t\t\tif(!fallback)\n");
	fprintf(output_file, "\t\t\t\tfallback = wiki_data_decompressed + wiki_entries[i].text_ofs;\n");
	fprintf(output_file, "\t\t}\n");
	fprintf(output_file, "\t}\n");
	fprintf(output_file, "\treturn fallback;\n");
	fprintf(output_file, "}\n");
	fprintf(output_file, "\n");

	/* Generate wiki_get_status function */
	fprintf(output_file, "int8_t wiki_get_status(const char *config, const char *section, const char *param)\n");
	fprintf(output_file, "{\n");
	fprintf(output_file, "\tif(!wiki_data_decompressed) return -1;\n");
	fprintf(output_file, "\tint32_t i, count = wiki_count();\n");
	fprintf(output_file, "\tint8_t fallback = -1;\n");
	fprintf(output_file, "\tfor(i = 0; i < count; i++)\n");
	fprintf(output_file, "\t{\n");
	fprintf(output_file, "\t\tconst char *e_config = wiki_data_decompressed + wiki_entries[i].config_ofs;\n");
	fprintf(output_file, "\t\tconst char *e_section = wiki_data_decompressed + wiki_entries[i].section_ofs;\n");
	fprintf(output_file, "\t\tconst char *e_param = wiki_data_decompressed + wiki_entries[i].param_ofs;\n");
	fprintf(output_file, "\t\tif(strcmp(e_config, config) == 0 && strcmp(e_param, param) == 0)\n");
	fprintf(output_file, "\t\t{\n");
	fprintf(output_file, "\t\t\tif(section && section[0] && strcmp(e_section, section) == 0)\n");
	fprintf(output_file, "\t\t\t\treturn wiki_entries[i].status;\n");
	fprintf(output_file, "\t\t\tif(fallback < 0)\n");
	fprintf(output_file, "\t\t\t\tfallback = wiki_entries[i].status;\n");
	fprintf(output_file, "\t\t}\n");
	fprintf(output_file, "\t}\n");
	fprintf(output_file, "\treturn fallback;\n");
	fprintf(output_file, "}\n");
#else
	fprintf(output_file, "void webif_wiki_prepare(void)\n");
	fprintf(output_file, "{\n");
	fprintf(output_file, "\tcs_log(\"wiki: %%d help entries loaded\", wiki_count());\n");
	fprintf(output_file, "}\n");
	fprintf(output_file, "\n");

	fprintf(output_file, "void webif_wiki_free(void)\n");
	fprintf(output_file, "{\n");
	fprintf(output_file, "\t/* nothing to free in uncompressed mode */\n");
	fprintf(output_file, "}\n");
	fprintf(output_file, "\n");

	fprintf(output_file, "const char *wiki_get_help(const char *config, const char *section, const char *param)\n");
	fprintf(output_file, "{\n");
	fprintf(output_file, "\tint32_t i;\n");
	fprintf(output_file, "\tint32_t count = wiki_count();\n");
	fprintf(output_file, "\tconst char *fallback = NULL;\n");
	fprintf(output_file, "\tfor(i = 0; i < count; i++)\n");
	fprintf(output_file, "\t{\n");
	fprintf(output_file, "\t\tif(strcmp(wiki_entries[i].config, config) == 0 &&\n");
	fprintf(output_file, "\t\t   strcmp(wiki_entries[i].param, param) == 0)\n");
	fprintf(output_file, "\t\t{\n");
	fprintf(output_file, "\t\t\tif(section && section[0] && strcmp(wiki_entries[i].section, section) == 0)\n");
	fprintf(output_file, "\t\t\t\treturn wiki_entries[i].text;\n");
	fprintf(output_file, "\t\t\tif(!fallback)\n");
	fprintf(output_file, "\t\t\t\tfallback = wiki_entries[i].text;\n");
	fprintf(output_file, "\t\t}\n");
	fprintf(output_file, "\t}\n");
	fprintf(output_file, "\treturn fallback;\n");
	fprintf(output_file, "}\n");
	fprintf(output_file, "\n");

	/* Generate wiki_get_status function */
	fprintf(output_file, "int8_t wiki_get_status(const char *config, const char *section, const char *param)\n");
	fprintf(output_file, "{\n");
	fprintf(output_file, "\tint32_t i;\n");
	fprintf(output_file, "\tint32_t count = wiki_count();\n");
	fprintf(output_file, "\tint8_t fallback = -1;\n");
	fprintf(output_file, "\tfor(i = 0; i < count; i++)\n");
	fprintf(output_file, "\t{\n");
	fprintf(output_file, "\t\tif(strcmp(wiki_entries[i].config, config) == 0 &&\n");
	fprintf(output_file, "\t\t   strcmp(wiki_entries[i].param, param) == 0)\n");
	fprintf(output_file, "\t\t{\n");
	fprintf(output_file, "\t\t\tif(section && section[0] && strcmp(wiki_entries[i].section, section) == 0)\n");
	fprintf(output_file, "\t\t\t\treturn wiki_entries[i].status;\n");
	fprintf(output_file, "\t\t\tif(fallback < 0)\n");
	fprintf(output_file, "\t\t\t\tfallback = wiki_entries[i].status;\n");
	fprintf(output_file, "\t\t}\n");
	fprintf(output_file, "\t}\n");
	fprintf(output_file, "\treturn fallback;\n");
	fprintf(output_file, "}\n");
#endif

	fprintf(output_file, "\n");
	fprintf(output_file, "#endif /* WEBIF && WEBIF_WIKI */\n");

	fclose(output_file);
}

int main(int argc, char *argv[])
{
	/* Allow overriding wiki directory via command line */
	if(argc > 1)
		{ wiki_dir = argv[1]; }

	/* Load is_defined.txt for filtering */
	readfile(is_defined_file, &is_defined_content, &is_defined_len);

	scan_wiki_directory(wiki_dir);

	if(wiki.num == 0)
	{
		fprintf(stderr, "Warning: No wiki entries found in %s\n", wiki_dir);
	}
	else
	{
		printf("WIKI\tProcessed %u entries: %u included, %u skipped (disabled in config)\n",
				stats_total, stats_included, stats_skipped);
	}

	generate_header();

	generate_source();

	if(is_defined_content)
		{ free(is_defined_content); }

	return 0;
}
