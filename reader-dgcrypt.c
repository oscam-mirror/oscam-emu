#include "globals.h"
#ifdef READER_DGCRYPT
#include "reader-common.h"

#define DEBUG 0

static const uint8_t dgcrypt_atr[8] = { 0x3B, 0xE9, 0x00, 0x00, 0x81, 0x31, 0xC3, 0x45 };
static const uint8_t cmd_CWKEY[5]   = { 0x81, 0xD0, 0x00, 0x01, 0x08 };
static const uint8_t cmd_CAID[5]   = { 0x81, 0xC0, 0x00, 0x01, 0x0A };
static const uint8_t cmd_SERIAL[5]  = { 0x81, 0xD1, 0x00, 0x01, 0x10 };
static const uint8_t cmd_CARD_ID[5]  = { 0x81, 0xD4, 0x00, 0x01, 0x05 };
static const uint8_t cmd_LABEL[5]   = { 0x81, 0xD2, 0x00, 0x01, 0x10 };
//static const uint8_t cmd_SUBSYS[5] = { 0x81, 0xDD, 0x00, 0x10, 0x04 };
static const uint8_t cmd_ECM[3]     = { 0x80, 0xEA, 0x80 };
static const uint8_t cmd_EMM[3]     = { 0x80, 0xEB, 0x80 };

struct dgcrypt_data
{
	uint8_t session_key[16];
};

static int32_t dgcrypt_cmd(struct s_reader *rdr, const uint8_t *buf, const int32_t buflen, uint8_t *response, uint16_t *response_length, uint16_t min_response_len)
{
	rdr->ifsc = 195;
	rdr->ns = 1;

	if(DEBUG)
	{
		char tmp[512];
		rdr_log(rdr, "SEND -> %s(%d)", cs_hexdump(1, buf, buflen, tmp, sizeof(tmp)), buflen);
	}
	int32_t ret = reader_cmd2icc(rdr, buf, buflen, response, response_length);

	if(DEBUG)
	{
		char tmp[512];
		rdr_log(rdr, "RECV <- %s(%d) ret=%d", cs_hexdump(1, response, *response_length, tmp, sizeof(tmp)), *response_length, ret);
	}
	// reader_cmd2icc retuns ERROR=1, OK=0 - the opposite of OK and ERROR defines in reader-common.h

	if(ret)
	{
		rdr_log(rdr, "ERROR: reader_cmd2icc() ret=%d", ret);
		return ERROR;
	}

	if(*response_length < 2 || *response_length < min_response_len)
	{
		if (response[0] == 0x6b && response[1] == 0x01) rdr_log(rdr, "ERROR: card has expired, please update your card");
		else rdr_log(rdr, "ERROR: response_length=%d < min_response_length=%d", *response_length, min_response_len);
		return ERROR; // Response is two short
	}

	if(response[*response_length - 2] != 0x90 || (response[*response_length - 1] != 0x00 && response[*response_length - 1] != 0x17))
	{
		rdr_log(rdr, "ERROR: response[-2] != 0x90 its 0x%02X", response[*response_length - 2]);
		rdr_log(rdr, "ERROR: response[-1] != 0x00 or 0x17 its 0x%02X", response[*response_length - 1]);
		return ERROR; // The reader responded with "command not OK"
	}
	return OK;
}

static int32_t dgcrypt_card_init(struct s_reader *rdr, ATR *newatr)
{
	def_resp

	get_atr
	if(atr_size < sizeof(dgcrypt_atr))
		{ return ERROR; }

	// Full ATR: 3B E9 00 00 81 31 C3 45 99 63 74 69 19 99 12 56 10 EC
	if(memcmp(atr, dgcrypt_atr, sizeof(dgcrypt_atr)) != 0)
		{ return ERROR; }

	if(!cs_malloc(&rdr->csystem_data, sizeof(struct dgcrypt_data)))
		{ return ERROR; }

	struct dgcrypt_data *csystem_data = rdr->csystem_data;

	rdr_log(rdr, "[dgcrypt-reader] card detected.");

	memset(rdr->sa, 0, sizeof(rdr->sa));
	memset(rdr->prid, 0, sizeof(rdr->prid));
	memset(rdr->hexserial, 0, sizeof(rdr->hexserial));
	memset(rdr->cardid, 0, sizeof(rdr->cardid));

	rdr->nprov = 1;
	// rdr->caid = 0x4ABF;

	// Get session key
	// Send: 81 D0 00 01 08
	// Recv: 32 86 17 D5 2C 66 61 14 90 00
	if(!dgcrypt_cmd(rdr, cmd_CWKEY, sizeof(cmd_CWKEY), cta_res, &cta_lr, 8))
		{ return ERROR; }
	memcpy(csystem_data->session_key + 0, cta_res, 8);
	memcpy(csystem_data->session_key + 8, cta_res, 8);

	// Get CAID
	// Send: 81 C0 00 01 0A
	// Recv: 4A BF 90 00
	if (!dgcrypt_cmd(rdr, cmd_CAID, sizeof(cmd_CAID), cta_res, &cta_lr, 2))
		{ return ERROR; }
	rdr->caid = (cta_res[0] << 8) | cta_res[1];

	// Get serial number
	// Send: 81 D1 00 01 10
	// Recv: 00 0D DB 08 71 0D D5 0C 30 30 30 30 30 30 30 30 90 00
	if(!dgcrypt_cmd(rdr, cmd_SERIAL, sizeof(cmd_SERIAL), cta_res, &cta_lr, 8))
		{ return ERROR; }
	memcpy(rdr->hexserial, cta_res + 1, 7);

	// Get card id
	// Send: 81 D4 00 01 05
	// Recv: 00 00 00 76 AC 90 00
	if(!dgcrypt_cmd(rdr, cmd_CARD_ID, sizeof(cmd_CARD_ID), cta_res, &cta_lr, 5))
		{ return ERROR; }
	memcpy(rdr->cardid, cta_res, 5);

	// Get LABEL
	// Send: 81 D2 00 01 10
	// Recv: 50 61 79 5F 54 56 5F 43 61 72 64 00 00 00 00 00 90 00
	// Txt: P  a  y  _  T  V  _  C  a  r  d
	if(!dgcrypt_cmd(rdr, cmd_LABEL, sizeof(cmd_LABEL), cta_res, &cta_lr, 16))
		{ return ERROR; }
	char label[17];
	memset(label, 0, sizeof(label));
	memcpy(label, cta_res, 16);

	// Get subsystem - !FIXME! We are not using the answer of this command!
	// Send: 81 DD 00 10 04
	// Recv: 00 55 00 55 90 00, also 00 8F 00 8F 90 00
	// if(!dgcrypt_cmd(rdr, cmd_LABEL, sizeof(cmd_LABEL), cta_res, &cta_lr, 4))
	// 	{ return ERROR; }

	rdr_log_sensitive(rdr, "CAID: 0x%04X, Serial: {%"PRIu64"} HexSerial: {%02X %02X %02X %02X %02X %02X %02X} Card Id: {%02X %02X %02X %02X %02X} Label: {%s}",
					rdr->caid,
					b2ll(7, rdr->hexserial),
					rdr->hexserial[0], rdr->hexserial[1], rdr->hexserial[2],
					rdr->hexserial[3], rdr->hexserial[4], rdr->hexserial[5], rdr->hexserial[6],
					rdr->cardid[0], rdr->cardid[1], rdr->cardid[2], rdr->cardid[3], rdr->cardid[4],
					label);

	return OK;
}

static int32_t dgcrypt_do_ecm(struct s_reader *rdr, const ECM_REQUEST *er, struct s_ecm_answer *ea)
{
	def_resp
	uint8_t cmd_buffer[256];
	struct dgcrypt_data *csystem_data = rdr->csystem_data;

	memcpy(cmd_buffer, er->ecm, er->ecm[2] + 3);
	// Replace The first 3 bytes of the ECM with the command
	memcpy(cmd_buffer, cmd_ECM, sizeof(cmd_ECM));

	// Write ECM
	// Send: 80 EA 80 00 55 00 00 3F 90 03 00 00 18 5D 82 4E 01 C4 2D 60 12 ED 34 37 ED 72 .. .. ..
	// Recv: 72 25 8D A1 0D 0D D2 44 EE ED 51 2F 3B 5D 19 63 E6 90 00
	if(!dgcrypt_cmd(rdr, cmd_buffer, er->ecm[2] + 3, cta_res, &cta_lr, 17))
		{ return ERROR; }

	if(cta_res[0] != 0x72) // CW response MUST start with 0x72
		{ return ERROR; }

	int i;
	for(i = 0; i < 16; i++)
	{
		ea->cw[i] = cta_res[1 + i] ^ csystem_data->session_key[i];
	}
	return OK;
}

static int32_t dgcrypt_do_emm(struct s_reader *rdr, EMM_PACKET *ep)
{
	def_resp
	uint8_t cmd_buffer[256];
	int32_t emm_length = ep->emm[2] + 3 + 2;

        // add 2 bytes for header
	memcpy(cmd_buffer + 2, ep->emm, emm_length);
	// Replace The first 3 bytes of the EMM with the command
	memcpy(cmd_buffer, cmd_EMM, sizeof(cmd_EMM));

	// Write EMM
	// Send: 80 EB 80 00 54 00 00 00 00 76 AC 00 8F 82 4A 90 03 00 00 .. .. ..
	// Recv: 90 17
	if(!dgcrypt_cmd(rdr, cmd_buffer, emm_length, cta_res, &cta_lr, 2))
		{ return ERROR; }

	return OK;
}

static int32_t dgcrypt_get_emm_type(EMM_PACKET *ep, struct s_reader *rdr)
{
	rdr_log_dbg(rdr, D_EMM, "Entered dgcrypt_get_emm_type ep->emm[0]=%x", ep->emm[0]);
	char tmp_dbg[10];

	switch(ep->emm[0])
	{
		case 0x82:
			ep->type = UNIQUE;
			memset(ep->hexserial, 0, 8);
			memcpy(ep->hexserial, ep->emm + 4, 5);

			rdr_log_dbg_sensitive(rdr, D_EMM, "UNIQUE, ep->hexserial = {%s}",
								cs_hexdump(1, ep->hexserial, 5, tmp_dbg, sizeof(tmp_dbg)));

			rdr_log_dbg_sensitive(rdr, D_EMM, "UNIQUE, rdr->cardid = {%s}",
								cs_hexdump(1, rdr->cardid, 5, tmp_dbg, sizeof(tmp_dbg)));

			return (!memcmp(rdr->cardid, ep->hexserial, 5));
			break;
			// Unknown EMM types, but allready subbmited to dev's
			// FIXME: Drop EMM's until there are implemented
		default:
			ep->type = UNKNOWN;
			return 1;
	}
}

static int32_t dgcrypt_get_emm_filter(struct s_reader *rdr, struct s_csystem_emm_filter **emm_filters, unsigned int *filter_count)
{
	if(*emm_filters == NULL)
	{
		// need more info
		//--|-|len|--|card id 5 byte|  const |len|const|--------------
		//82 00 54 00 00 00 00 xx xx 00 8f 82 4a 90 03 ...  tested, works
		//82 00 64 00 00 00 00 00 00 00 8f 82 5a ff ff ...  ? filler
		//82 00 34 00 00 00 00 xx xx 00 8f 82 2a 90 03 ...  ?
		//82 00 37 00 00 00 00 xx xx 00 8f 82 2d 90 03 ...  ?

		const unsigned int max_filter_count = 1; // fixme
		if(!cs_malloc(emm_filters, max_filter_count * sizeof(struct s_csystem_emm_filter)))
		{
			return ERROR;
		}

		struct s_csystem_emm_filter *filters = *emm_filters;

		int32_t idx = 0;

		filters[idx].type = EMM_UNIQUE;
		filters[idx].enabled = 1;
		filters[idx].filter[0] = 0x82;
		filters[idx].mask[0] = 0xFF;
		memcpy(&filters[idx].filter[2], rdr->cardid, 5);
		memset(&filters[idx].mask[2], 0xFF, 5);
		idx++;
/*
		// I've never seen it
		filters[idx].type = EMM_GLOBAL;
		filters[idx].enabled = 1;
		filters[idx].filter[0] = 0x83;
		filters[idx].mask[0] = 0xFF;
		idx++;
*/
		*filter_count = idx;
	}
	return OK;
}

const struct s_cardsystem reader_dgcrypt =
{
	.desc           = "dgcrypt",
	.caids          = (uint16_t[]){ 0x4AB0, 0x4ABF, 0 },
	.card_init      = dgcrypt_card_init,
	.do_emm         = dgcrypt_do_emm,
	.do_ecm         = dgcrypt_do_ecm,
	.get_emm_type   = dgcrypt_get_emm_type,
	.get_emm_filter = dgcrypt_get_emm_filter,
};

#endif
