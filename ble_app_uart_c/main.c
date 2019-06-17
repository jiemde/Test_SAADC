/**
 * Copyright (c) 2016 - 2017, Nordic Semiconductor ASA
 * 
 * All rights reserved.
 * 
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 * 
 * 1. Redistributions of source code must retain the above copyright notice, this
 *    list of conditions and the following disclaimer.
 * 
 * 2. Redistributions in binary form, except as embedded into a Nordic
 *    Semiconductor ASA integrated circuit in a product or a software update for
 *    such product, must reproduce the above copyright notice, this list of
 *    conditions and the following disclaimer in the documentation and/or other
 *    materials provided with the distribution.
 * 
 * 3. Neither the name of Nordic Semiconductor ASA nor the names of its
 *    contributors may be used to endorse or promote products derived from this
 *    software without specific prior written permission.
 * 
 * 4. This software, with or without modification, must only be used with a
 *    Nordic Semiconductor ASA integrated circuit.
 * 
 * 5. Any software provided in binary form under this license must not be reverse
 *    engineered, decompiled, modified and/or disassembled.
 * 
 * THIS SOFTWARE IS PROVIDED BY NORDIC SEMICONDUCTOR ASA "AS IS" AND ANY EXPRESS
 * OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY, NONINFRINGEMENT, AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL NORDIC SEMICONDUCTOR ASA OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
 * CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
 * GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
 * OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * 
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include "nordic_common.h"
#include "app_error.h"
#include "app_uart.h"
#include "ble_db_discovery.h"
#include "app_timer.h"
#include "app_util.h"
#include "bsp_btn_ble.h"
#include "ble.h"
#include "ble_gap.h"
#include "ble_hci.h"
#include "nrf_sdh.h"
#include "nrf_sdh_ble.h"
#include "nrf_sdh_soc.h"
#include "nrf_pwr_mgmt.h"
#include "ble_advdata.h"
#include "ble_nus_c.h"
#include "nrf_ble_gatt.h"
#include "math.h"
#include "nrf_delay.h"

#include "nrf_log.h"
#include "nrf_log_ctrl.h"
#include "nrf_log_default_backends.h"

#include "nrf_gpio.h"
#include "nrf_drv_spis.h"
#include "boards.h"

#define SPIS_INSTANCE 1	 															/**< SPIS instance index. */
static const nrf_drv_spis_t spis = NRF_DRV_SPIS_INSTANCE(SPIS_INSTANCE);			/**< SPIS instance. */

#define TEST_STRING "853"

static uint8_t       	m_tx_buf_debug[] = TEST_STRING;           							/**< TX buffer for debug. */
static uint8_t       	m_rx_buf_debug[8];    												/**< RX buffer for debug. */
static const uint8_t 	m_length_tx_debug = sizeof(m_tx_buf_debug);        					/**< Transfer length for debug. */
static const uint8_t 	m_length_rx_debug = sizeof(m_rx_buf_debug) - 1;        				/**< Receive length for debug. */

static uint8_t*	    	m_tx_buf;         									/**< TX buffer. */
static uint8_t 		m_length_tx = 0;        												/**< Transfer length. */
static uint8_t     	m_rx_buf[256];    														/**< RX buffer. */
static uint8_t 		m_length_rx = sizeof(m_rx_buf) - 1;        								/**< Receive length. */

nrf_mutex_t m_mutex;
uint8_t is_nested;

static volatile bool debug = true; 									/**< Flag mis a true pour des logs ou des if condition que je veux seulement en debug mode. */
static volatile bool gap_unique_connection = true;				/**< Flag mis a true pour connection automatique au premier Nordic percu avec le UUID. */
static volatile bool do_connect = false; 							/**< Flag mis a true lorsqu'une adresse MAC a ete recu du SPI buffer m_rx_buf. */
static volatile bool spis_xfer_done = true; 						/**< Flag used to indicate that SPIS instance completed the transfer. */

static uint8_array_t adv_data;

static uint32_t ticks; 											/**< Nombre de ticks pour le retour de la fonction app_timer_cnt_get necessaire pour le debug */
static uint8_t sampling_frequency[6]; 							/**< Frequence d'echantillonnage qui sera envoye par BLE au peripherique qui echantillonne */
static uint8_t connecting_mac_addr[7];							/**< Tableau contenant la MAC address qui est recu sur le SPI slave */

#define APP_BLE_CONN_CFG_TAG    	1                                	/**< A tag that refers to the BLE stack configuration we set with @ref sd_ble_cfg_set. Default tag is @ref BLE_CONN_CFG_TAG_DEFAULT. */
#define APP_BLE_OBSERVER_PRIO   3                                  	/**< Application's BLE observer priority. You shoulnd't need to modify this value. */

#define UART_TX_BUF_SIZE      32                                     /**< UART TX buffer size. */
#define UART_RX_BUF_SIZE	32                                     /**< UART RX buffer size. */

#define NUS_SERVICE_UUID_TYPE   BLE_UUID_TYPE_VENDOR_BEGIN              /**< UUID type for the Nordic UART Service (vendor specific). */

#define SCAN_INTERVAL           	0x00A0                                  	/**< Determines scan interval in units of 0.625 millisecond. */
#define SCAN_WINDOW             	0x0050                                  	/**< Determines scan window in units of 0.625 millisecond. */
#define SCAN_TIMEOUT            	0x0000                             		/**< Timout when scanning. 0x0000 disables timeout. */

#define MIN_CONNECTION_INTERVAL MSEC_TO_UNITS(7.5, UNIT_1_25_MS)        	/**< Determines minimum connection interval in millisecond. */
#define MAX_CONNECTION_INTERVAL MSEC_TO_UNITS(10, UNIT_1_25_MS)         	/**< Determines maximum connection interval in millisecond. */
#define SLAVE_LATENCY           0                                       						/**< Determines slave latency in counts of connection events. */
#define SUPERVISION_TIMEOUT     MSEC_TO_UNITS(4000, UNIT_10_MS)         	/**< Determines supervision time-out in units of 10 millisecond. */

#define UUID16_SIZE             2                                       		/**< Size of 16 bit UUID (bytes)*/ 
#define UUID32_SIZE             4                                       		/**< Size of 32 bit UUID */
#define UUID128_SIZE            16                                      		/**< Size of 128 bit UUID */

#define ECHOBACK_BLE_UART_DATA  0                       	/**< Echo the UART data that is received over the Nordic UART Service back to the sender. */

BLE_NUS_C_DEF(m_ble_nus_c);                                     	/**< BLE NUS service client instance. */
NRF_BLE_GATT_DEF(m_gatt);                                         	/**< GATT module instance. */
BLE_DB_DISCOVERY_DEF(m_db_disc);                         	/**< DB discovery module instance. */

static uint16_t m_ble_nus_max_data_len = BLE_GATT_ATT_MTU_DEFAULT - OPCODE_LENGTH - HANDLE_LENGTH; 	/**< Maximum length of data (in bytes) that can be transmitted to the peer by the Nordic UART service module (20 bytes) can be changed. */

/**@brief Structure gerant un element de la FIFO
 *
 * @url https://openclassrooms.com/fr/courses/19980-apprenez-a-programmer-en-c/19868-les-piles-et-les-files
 */
typedef struct Element Element;
struct Element
{
    uint8_t nombre[8];
    Element *suivant;
};

/**@brief Structure gerant une FIFO
 *
 * @url https://openclassrooms.com/fr/courses/19980-apprenez-a-programmer-en-c/19868-les-piles-et-les-files
 */
typedef struct File File;
struct File
{
    Element *premier;
};

static File fifo;					/**< FIFO utilisee dans le code pour MAC address et reception BLE. */		
static int taille_fifo = 0;			/**< Taille de la FIFO. */

static File fifo_mac;					/**< FIFO utilisee dans le code pour MAC address et reception BLE. */		
static int taille_fifo_mac = 0;			/**< Taille de la FIFO. */

/**@brief Fonction ajoutant un element a la FIFO
 *
 * @params[in] File ; File dans laquelle on veut ajouter un element 
 *
 * @params[in] nvNombre ; Tableau a ajouter
 *
 * @url https://openclassrooms.com/fr/courses/19980-apprenez-a-programmer-en-c/19868-les-piles-et-les-files
 *
 * @return Retourne NULL si erreur, 1 sinon
 */
int enfiler(File *file, uint8_t nvNombre[8])
{
	Element *nouveau = malloc(sizeof(*nouveau));
	if (file == NULL || nouveau == NULL)
	{
		return NULL;
	}

	memcpy(nouveau->nombre, nvNombre, 8);
	nouveau->suivant = NULL;

	if (file->premier != NULL) /* La file n'est pas vide */
	{
		/* On se positionne a la fin de la file */
		Element *elementActuel = file->premier;
		while (elementActuel->suivant != NULL)
		{
		elementActuel = elementActuel->suivant;
		}
		elementActuel->suivant = nouveau;
		return 1;
	}
	else /* La file est vide, notre element est le premier */
	{
		file->premier = nouveau;
		return 1;
	}
}

/**@brief Fonction enlevant un element de la FIFO
 *
 * @params[in] File ; File dans laquelle on veut enlever un element
 *
 * @url https://openclassrooms.com/fr/courses/19980-apprenez-a-programmer-en-c/19868-les-piles-et-les-files
 *
 * @return Retourne le tableau enleve de la file ou NULL si FIFO est vide
 */
uint8_t* defiler(File *file)
{
	if (file == NULL)
	{
		return NULL;
	}

	static uint8_t nombreDefile[8];

	/* On verifie s'il y a quelque chose a defiler */
	if (file->premier != NULL)
	{
		Element *elementDefile = file->premier;

		memcpy(nombreDefile, elementDefile->nombre, 8);
		file->premier = elementDefile->suivant;
		free(elementDefile);
	}

	return nombreDefile;
}



/**@brief Connection parameters requested for connection. */
static ble_gap_conn_params_t const m_connection_param =
{
	(uint16_t)MIN_CONNECTION_INTERVAL,  		// Minimum connection
	(uint16_t)MAX_CONNECTION_INTERVAL,  		// Maximum connection
	(uint16_t)SLAVE_LATENCY,            				// Slave latency
	(uint16_t)SUPERVISION_TIMEOUT       			// Supervision time-out
};

/** @brief Parameters used when scanning. */
static ble_gap_scan_params_t const m_scan_params =
{
	.active   = 1,
	.interval = SCAN_INTERVAL,
	.window   = SCAN_WINDOW,
	.timeout  = SCAN_TIMEOUT,
	#if (NRF_SD_BLE_API_VERSION <= 2)
	  .selective   = 0,
	  .p_whitelist = NULL,
	#endif
	#if (NRF_SD_BLE_API_VERSION >= 3)
	  .use_whitelist = 0,
	#endif
};

/**@brief NUS uuid. */
static ble_uuid_t const m_nus_uuid =
{
	.uuid = BLE_UUID_NUS_SERVICE,
	.type = NUS_SERVICE_UUID_TYPE
};


/**@brief Function for asserts in the SoftDevice.
 *
 * @details This function will be called in case of an assert in the SoftDevice.
 *
 * @warning This handler is an example only and does not fit a final product. You need to analyze
 *          how your product is supposed to react in case of Assert.
 * @warning On assert from the SoftDevice, the system can only recover on reset.
 *
 * @param[in] line_num     Line number of the failing ASSERT call.
 * @param[in] p_file_name  File name of the failing ASSERT call.
 */
void assert_nrf_callback(uint16_t line_num, const uint8_t * p_file_name)
{
	app_error_handler(0xDEADBEEF, line_num, p_file_name);
}


/**@brief Function to start scanning. */
static void scan_start(void)
{
	ret_code_t ret;

	ret = sd_ble_gap_scan_start(&m_scan_params);
	APP_ERROR_CHECK(ret);

	ret = bsp_indication_set(BSP_INDICATE_SCANNING);
	APP_ERROR_CHECK(ret);
}


/**@brief Function for handling database discovery events.
 *
 * @details This function is callback function to handle events from the database discovery module.
 *          Depending on the UUIDs that are discovered, this function should forward the events
 *          to their respective services.
 *
 * @param[in] p_event  Pointer to the database discovery event.
 */
static void db_disc_handler(ble_db_discovery_evt_t * p_evt)
{
	ble_nus_c_on_db_disc_evt(&m_ble_nus_c, p_evt);
}



/**@brief   Function for handling app_uart events.
 *
 * @details This function will receive a single character from the app_uart module and append it to
 *          a string. The string will be be sent over BLE when the last character received was a
 *          'new line' '\n' (hex 0x0A) or if the string has reached the maximum data length.
 */
void uart_event_handle(app_uart_evt_t * p_event)
{
	static uint8_t data_array[BLE_NUS_MAX_DATA_LEN];
	static uint16_t index = 0;
	uint32_t ret_val;

	switch (p_event->evt_type)
	{
		/**@snippet [Handling data from UART] */
		case APP_UART_DATA_READY:
			UNUSED_VARIABLE(app_uart_get(&data_array[index]));
			index++;

			if ((data_array[index - 1] == '\n') || (index >= (m_ble_nus_max_data_len)))
			{
				NRF_LOG_INFO("Ready to send data over BLE NUS");
				NRF_LOG_HEXDUMP_DEBUG(data_array, index);

				do
				{
					ret_val = ble_nus_c_string_send(&m_ble_nus_c, data_array, index);
					if ( (ret_val != NRF_ERROR_INVALID_STATE) && (ret_val != NRF_ERROR_BUSY) )
					{
						APP_ERROR_CHECK(ret_val);
					}
				} while (ret_val == NRF_ERROR_BUSY);
				
				index = 0;
			}
			break;

		/**@snippet [Handling data from UART] */
		case APP_UART_COMMUNICATION_ERROR:
			NRF_LOG_ERROR("Communication error occurred while handling UART.");
			APP_ERROR_HANDLER(p_event->data.error_communication);
			break;

		case APP_UART_FIFO_ERROR:
			NRF_LOG_ERROR("Error occurred in FIFO module used by UART.");
			APP_ERROR_HANDLER(p_event->data.error_code);
			break;

		default:
			break;
	}
}



/**@brief Callback handling NUS Client events.
 *
 * @details This function is called to notify the application of NUS client events.
 *
 * @param[in]   p_ble_nus_c   NUS Client Handle. This identifies the NUS client
 * @param[in]   p_ble_nus_evt Pointer to the NUS Client event.
 */

/**@snippet [Handling events from the ble_nus_c module] */
static void ble_nus_c_evt_handler(ble_nus_c_t * p_ble_nus_c, ble_nus_c_evt_t const * p_ble_nus_evt)
{
//	NRF_LOG_INFO("NUS");
	ret_code_t err_code;

	switch (p_ble_nus_evt->evt_type)
	{
		case BLE_NUS_C_EVT_DISCOVERY_COMPLETE:
			NRF_LOG_INFO("Discovery complete.");
			err_code = ble_nus_c_handles_assign(p_ble_nus_c, p_ble_nus_evt->conn_handle, &p_ble_nus_evt->handles);
			APP_ERROR_CHECK(err_code);

			err_code = ble_nus_c_tx_notif_enable(p_ble_nus_c);
			APP_ERROR_CHECK(err_code);
			NRF_LOG_INFO("Connected to device with Nordic UART Service.");
			break;

		case BLE_NUS_C_EVT_NUS_TX_EVT: 
		{
			// En gros, seulement utiliser pour l'acquisition des valeurs du SAADC de l'autre module BLE
			// Met la valeur acquise directement dans la FIFO qui elle sera traitee dans la fonction main()
			
			char* temp;
			memset(temp, 0, p_ble_nus_evt->data_len);
			memcpy(temp, p_ble_nus_evt->p_data, p_ble_nus_evt->data_len);
			
//			NRF_LOG_INFO("Length = %d", p_ble_nus_evt->data_len);
			
//			NRF_LOG_INFO("%02x %02x %02x %02x %02x", p_ble_nus_evt->p_data[0], p_ble_nus_evt->p_data[1], p_ble_nus_evt->p_data[2], p_ble_nus_evt->p_data[3], p_ble_nus_evt->p_data[4]);
//			NRF_LOG_INFO("%02x %02x %02x %02x %02x", p_ble_nus_evt->p_data[5], p_ble_nus_evt->p_data[6], p_ble_nus_evt->p_data[7], p_ble_nus_evt->p_data[8], p_ble_nus_evt->p_data[9]);			
			
			if(debug)
			{
				ticks = app_timer_cnt_get();
				ticks = (int) ((ticks * 1000) / 32768);
				NRF_LOG_INFO("%i	%s", (int)ticks, (uint32_t)temp);
//				NRF_LOG_HEXDUMP_INFO(p_ble_nus_evt->p_data, p_ble_nus_evt->data_len);
			}
			
//			for(int i = p_ble_nus_evt->data_len; i < 8; i++)
//			{
//				temp[i] = 0x00;
//			}
////			
//			if(taille_fifo < 1000000) // Nombre pris au hasard pour limiter la taille de la FIFO
//			{
//				sd_nvic_critical_region_enter(&is_nested);
//				int i = enfiler(&fifo, (uint8_t*)temp);
//				sd_nvic_critical_region_exit(is_nested);
//				taille_fifo++;
//				
////				if(i == NULL)
////				{
////					NRF_LOG_INFO("Error");
////				}
//			}
//			else
//			{
//				NRF_LOG_INFO("FIFO pleine");
//			}

//			NRF_LOG_HEXDUMP_INFO(m_tx_buf, m_length_tx);
//			NRF_LOG_INFO("Length : %d.", p_ble_nus_evt->data_len);
//			memcpy( (char *)p_ble_nus_evt->p_data, &temp, p_ble_nus_evt->data_len);
//			NRF_LOG_INFO("UART received : %s.", temp);
//			ble_nus_chars_received_uart_print(p_ble_nus_evt->p_data, p_ble_nus_evt->data_len);
			break;
		}

		case BLE_NUS_C_EVT_DISCONNECTED:
			NRF_LOG_INFO("Disconnected.");
			memset(m_rx_buf, 0, 256);
			do_connect = false;
			for(int i = 0; i < taille_fifo; i++)
			{
				defiler(&fifo);
			}
			taille_fifo = 0;
			scan_start();
			break;
	}
}
/**@snippet [Handling events from the ble_nus_c module] */

/** @brief Function for shutdown events.
 *
 * @param[in]   event       Shutdown type.
 */
static bool shutdown_handler(nrf_pwr_mgmt_evt_t event)
{
	ret_code_t err_code;

	err_code = bsp_indication_set(BSP_INDICATE_IDLE);
	APP_ERROR_CHECK(err_code);

	switch (event)
	{
		case NRF_PWR_MGMT_EVT_PREPARE_WAKEUP:
			// Prepare wakeup buttons.
			err_code = bsp_btn_ble_sleep_mode_prepare();
			APP_ERROR_CHECK(err_code);
			break;

		default:
			break;
	}
	return true;
}

NRF_PWR_MGMT_HANDLER_REGISTER(shutdown_handler, APP_SHUTDOWN_HANDLER_PRIORITY);

/**@brief Reads an advertising report and checks if a UUID is present in the service list.
 *
 * @details The function is able to search for 16-bit, 32-bit and 128-bit service UUIDs.
 *          To see the format of a advertisement packet, see
 *          https://www.bluetooth.org/Technical/AssignedNumbers/generic_access_profile.htm
 *
 * @param[in]   p_target_uuid The UUID to search for.
 * @param[in]   p_adv_report  Pointer to the advertisement report.
 *
 * @retval      true if the UUID is present in the advertisement report. Otherwise false
 */
static bool is_uuid_present(ble_uuid_t               const * p_target_uuid,
                            ble_gap_evt_adv_report_t const * p_adv_report)
{
	ret_code_t   err_code;
	ble_uuid_t   extracted_uuid;
	uint16_t     index  = 0;
	uint8_t    * p_data = (uint8_t *)p_adv_report->data;

	while (index < p_adv_report->dlen)
	{
		uint8_t field_length = p_data[index];
		uint8_t field_type   = p_data[index + 1];

		if ((field_type == BLE_GAP_AD_TYPE_16BIT_SERVICE_UUID_MORE_AVAILABLE) || (field_type == BLE_GAP_AD_TYPE_16BIT_SERVICE_UUID_COMPLETE))
		{
			for (uint32_t i = 0; i < (field_length / UUID16_SIZE); i++)
			{
				err_code = sd_ble_uuid_decode(UUID16_SIZE,
								    &p_data[i * UUID16_SIZE + index + 2],
								    &extracted_uuid);

				if (err_code == NRF_SUCCESS)
				{
					if (extracted_uuid.uuid == p_target_uuid->uuid)
					{
						return true;
					}
				}
			}
		}
		else if ((field_type == BLE_GAP_AD_TYPE_32BIT_SERVICE_UUID_MORE_AVAILABLE) || (field_type == BLE_GAP_AD_TYPE_32BIT_SERVICE_UUID_COMPLETE))
		{
			for (uint32_t i = 0; i < (field_length / UUID32_SIZE); i++)
			{
				err_code = sd_ble_uuid_decode(UUID32_SIZE,
							    &p_data[i * UUID32_SIZE + index + 2],
							    &extracted_uuid);

				if (err_code == NRF_SUCCESS)
				{
					if ((extracted_uuid.uuid == p_target_uuid->uuid) && (extracted_uuid.type == p_target_uuid->type))
					{
						return true;
					}
				}
			}
		}

		else if ((field_type == BLE_GAP_AD_TYPE_128BIT_SERVICE_UUID_MORE_AVAILABLE) || (field_type == BLE_GAP_AD_TYPE_128BIT_SERVICE_UUID_COMPLETE))
		{
			err_code = sd_ble_uuid_decode(UUID128_SIZE, &p_data[index + 2], &extracted_uuid);
			if (err_code == NRF_SUCCESS)
			{
				if ((extracted_uuid.uuid == p_target_uuid->uuid) && (extracted_uuid.type == p_target_uuid->type))
				{
					return true;
				}
			}
		}
		index += field_length + 1;
	}
	return false;
}


/** @brief Parses advertisement data, providing length and location of the field in case matching data is found. (used to get the DEVICE_NAME of the peripheral)
 *
 * @param[in]  type       Type of data to be looked for in advertisement data.
 * @param[in]  p_advdata  Advertisement report length and pointer to report.
 * @param[out] p_typedata If data type requested is found in the data report, type data length and
 *                        pointer to data will be populated here.
 *
 * @retval NRF_SUCCESS if the data type is found in the report.
 * @retval NRF_ERROR_NOT_FOUND if the data type could not be found.
 */
static uint32_t adv_report_parse(uint8_t type, uint8_array_t * p_advdata, uint8_array_t * p_typedata)
{
    uint32_t  index = 0;
    uint8_t * p_data;

    p_data = p_advdata->p_data;

    while (index < p_advdata->size)
    {
        uint8_t field_length = p_data[index];
        uint8_t field_type   = p_data[index + 1];

        if (field_type == type)
        {
            p_typedata->p_data = &p_data[index + 2];
            p_typedata->size   = field_length - 1;
            return NRF_SUCCESS;
        }
        index += field_length + 1;
    }
    return NRF_ERROR_NOT_FOUND;
}

/**@brief Function for handling BLE events.
 *
 * @param[in]   p_ble_evt   Bluetooth stack event.
 * @param[in]   p_context   Unused.
 */
static void ble_evt_handler(ble_evt_t const * p_ble_evt, void * p_context)
{
	ret_code_t            err_code;
	ble_gap_evt_t const * p_gap_evt = &p_ble_evt->evt.gap_evt;

	switch (p_ble_evt->header.evt_id)
	{
		case BLE_GAP_EVT_ADV_REPORT: // Case qui est appele lors de la sequence de scan du main
		{
			ble_gap_evt_adv_report_t const * p_adv_report = &p_gap_evt->params.adv_report;
						
			if(gap_unique_connection == true) // If condition selon flag decrit plus haut
			{
				do_connect = true;
				// Prepare advertisement report for parsing.
//				memcpy(adv_data.p_data, (uint8_t *)p_gap_evt->params.adv_report.data, p_gap_evt->params.adv_report.dlen);
//				adv_data.size = p_gap_evt->params.adv_report.dlen;
				if (is_uuid_present(&m_nus_uuid, p_adv_report)) // Fonction qui verifie si le UUID predefini par le vendeur (pour l'instant) est pareil au UUID des modules BLE autour 
				{
					// Get the device name of the peripheral
//					uint8_array_t device_name; 
//					uint32_t err_code2;
//					
//					err_code2 = adv_report_parse(BLE_GAP_AD_TYPE_COMPLETE_LOCAL_NAME, &adv_data, &device_name);
//					
//					if (err_code != NRF_SUCCESS)
//					{
//						// Look for the short local name if it was not found as complete.
//						err_code = adv_report_parse(BLE_GAP_AD_TYPE_SHORT_LOCAL_NAME, &adv_data, &device_name);
//						if (err_code != NRF_SUCCESS)
//						{
//							// If we can't parse the data, then exit.
//							NRF_LOG_INFO("Wrong");
//							return;
//						}
//					}
					
//					NRF_LOG_INFO("Length = %d", device_name.size);
					
					do_connect = true;
					err_code = sd_ble_gap_connect(&p_adv_report->peer_addr,
						    &m_scan_params,
						    &m_connection_param,
						    APP_BLE_CONN_CFG_TAG);

					if (err_code == NRF_SUCCESS)
					{
						// Scan is automatically stopped by the connect
						NRF_LOG_INFO("Connecting to target %02x%02x%02x%02x%02x%02x",
						     p_adv_report->peer_addr.addr[0],
						     p_adv_report->peer_addr.addr[1],
						     p_adv_report->peer_addr.addr[2],
						     p_adv_report->peer_addr.addr[3],
						     p_adv_report->peer_addr.addr[4]
						);

						err_code = bsp_indication_set(BSP_INDICATE_IDLE);
						APP_ERROR_CHECK(err_code);
						break;
					}
				}
			}
			else
			{
				if(is_uuid_present(&m_nus_uuid, p_adv_report) && taille_fifo_mac < 32) // Taille FIFO prise au hasard pour limiter le temps d'acquisition des modules BLE autour
				{
					NRF_LOG_INFO("Found target %02x%02x%02x%02x%02x%02x",
						     p_adv_report->peer_addr.addr[0],
						     p_adv_report->peer_addr.addr[1],
						     p_adv_report->peer_addr.addr[2],
						     p_adv_report->peer_addr.addr[3],
						     p_adv_report->peer_addr.addr[4],
						     p_adv_report->peer_addr.addr[5]
						     );
					
					uint8_t temp[8];
					memcpy(temp, p_adv_report->peer_addr.addr, 6);
					temp[6] = 0x00; 
					temp[7] = 0x00;
					
					int i = enfiler(&fifo_mac, temp);
					int j = enfiler(&fifo, temp);
					if(i == NULL || j == NULL)
					{
						NRF_LOG_INFO("Error");
					}
					taille_fifo_mac++;
					taille_fifo++;
					
//					NRF_LOG_INFO("%02x%02x%02x%02x", temp[0], temp[1], temp[2], temp[3])
//					NRF_LOG_INFO("%02x%02x%02x%02x", temp[4], temp[5], temp[6], temp[7]);
					
				}
				
				if(taille_fifo_mac >= 32 && do_connect == false)
				{
					//On attend la reception d'une MAC address valide du SPI master
					uint8_t* mac = defiler(&fifo_mac);
					if(memcmp(mac, connecting_mac_addr, 7) == 0)
					{
						memcpy(connecting_mac_addr, mac, 7);
						do_connect = true;
						break;
					}
					enfiler(&fifo_mac, mac);
				}
				
				if(do_connect) // On a eu une correspondance element FIFO/buffer rx SPI slave
				{
					NRF_LOG_INFO("Do connect");
					ble_gap_addr_t temp;
					memcpy(temp.addr, connecting_mac_addr, 6);
					temp.addr_type = 0x01;
					temp.addr_id_peer = 0x00;
					
					err_code = sd_ble_gap_connect(&temp,
						    &m_scan_params,
						    &m_connection_param,
						    APP_BLE_CONN_CFG_TAG);

					if (err_code == NRF_SUCCESS)
					{
						// Scan is automatically stopped by the connect
						NRF_LOG_INFO("Connecting to target %02x%02x%02x%02x%02x%02x",
							temp.addr[0], temp.addr[1], temp.addr[2], temp.addr[3], temp.addr[4], temp.addr[5]);

						err_code = bsp_indication_set(BSP_INDICATE_IDLE);
						APP_ERROR_CHECK(err_code);
						break;
					}
					
					for(int i = 0; i < taille_fifo_mac; i++) // Vider la file
					{
						defiler(&fifo_mac);
					}
					taille_fifo_mac = 0;
				}
			}
		}break; // BLE_GAP_EVT_ADV_REPORT

		case BLE_GAP_EVT_CONNECTED:
			NRF_LOG_INFO("Connected to target");
			err_code = ble_nus_c_handles_assign(&m_ble_nus_c, p_ble_evt->evt.gap_evt.conn_handle, NULL);
			APP_ERROR_CHECK(err_code);

			err_code = bsp_indication_set(BSP_INDICATE_CONNECTED);
			APP_ERROR_CHECK(err_code);

			// Start discovery of services. The NUS Client waits for a discovery result
			err_code = ble_db_discovery_start(&m_db_disc, p_ble_evt->evt.gap_evt.conn_handle);
			APP_ERROR_CHECK(err_code);
			break;

		case BLE_GAP_EVT_TIMEOUT:
			if (p_gap_evt->params.timeout.src == BLE_GAP_TIMEOUT_SRC_SCAN)
			{
				NRF_LOG_INFO("Scan timed out.");
				scan_start();
			}
			else if (p_gap_evt->params.timeout.src == BLE_GAP_TIMEOUT_SRC_CONN)
			{
				NRF_LOG_INFO("Connection Request timed out.");
			}
			break;

		case BLE_GAP_EVT_SEC_PARAMS_REQUEST:
			// Pairing not supported
			err_code = sd_ble_gap_sec_params_reply(p_ble_evt->evt.gap_evt.conn_handle, BLE_GAP_SEC_STATUS_PAIRING_NOT_SUPP, NULL, NULL);
			APP_ERROR_CHECK(err_code);
			break;

		case BLE_GAP_EVT_CONN_PARAM_UPDATE_REQUEST:
			// Accepting parameters requested by peer.
			err_code = sd_ble_gap_conn_param_update(p_gap_evt->conn_handle,
									    &p_gap_evt->params.conn_param_update_request.conn_params);
			APP_ERROR_CHECK(err_code);
			break;

		#ifndef S140
		case BLE_GAP_EVT_PHY_UPDATE_REQUEST:
			{
			NRF_LOG_DEBUG("PHY update request.");
			ble_gap_phys_t const phys =
			{
				.rx_phys = BLE_GAP_PHY_AUTO,
				.tx_phys = BLE_GAP_PHY_AUTO,
			};
			err_code = sd_ble_gap_phy_update(p_ble_evt->evt.gap_evt.conn_handle, &phys);
			APP_ERROR_CHECK(err_code);
			} break;
		#endif

		case BLE_GATTC_EVT_TIMEOUT:
			// Disconnect on GATT Client timeout event.
			NRF_LOG_DEBUG("GATT Client Timeout.");
			err_code = sd_ble_gap_disconnect(p_ble_evt->evt.gattc_evt.conn_handle,
								   BLE_HCI_REMOTE_USER_TERMINATED_CONNECTION);
			APP_ERROR_CHECK(err_code);
			break;

		case BLE_GATTS_EVT_TIMEOUT:
			// Disconnect on GATT Server timeout event.
			NRF_LOG_DEBUG("GATT Server Timeout.");
			err_code = sd_ble_gap_disconnect(p_ble_evt->evt.gatts_evt.conn_handle,
								   BLE_HCI_REMOTE_USER_TERMINATED_CONNECTION);
			APP_ERROR_CHECK(err_code);
			break;

		default:
			break;
	}
}

/**@brief Function for handling events from the GATT library. */
void gatt_evt_handler(nrf_ble_gatt_t * p_gatt, nrf_ble_gatt_evt_t const * p_evt)
{
	if (p_evt->evt_id == NRF_BLE_GATT_EVT_ATT_MTU_UPDATED)
	{
		NRF_LOG_INFO("ATT MTU exchange completed.");

		m_ble_nus_max_data_len = p_evt->params.att_mtu_effective - OPCODE_LENGTH - HANDLE_LENGTH;
		NRF_LOG_INFO("Ble NUS max data length set to 0x%X(%d)", m_ble_nus_max_data_len, m_ble_nus_max_data_len);
	}
}


/**@brief Function for handling events from the BSP module.
 *
 * @param[in] event  Event generated by button press.
 */
void bsp_event_handler(bsp_event_t event)
{
	ret_code_t err_code;

	switch (event)
	{
		case BSP_EVENT_SLEEP:
			nrf_pwr_mgmt_shutdown(NRF_PWR_MGMT_SHUTDOWN_GOTO_SYSOFF);
			break;

		case BSP_EVENT_DISCONNECT:
			err_code = sd_ble_gap_disconnect(m_ble_nus_c.conn_handle, BLE_HCI_REMOTE_USER_TERMINATED_CONNECTION);
		
			if (err_code != NRF_ERROR_INVALID_STATE)
			{
				APP_ERROR_CHECK(err_code);
			}
			break;

		case BSP_EVENT_KEY_2: // Button 3 on the board (utile pour debugger
		{			
			NRF_LOG_INFO("BSP EVENT");
//			m_rx_buf[0] = 0xFF; m_rx_buf[1] = 0xA7; m_rx_buf[2] = 0x8F; m_rx_buf[3] = 0x93;
//			m_rx_buf[4] = 0xD0; m_rx_buf[5] = 0x12; m_rx_buf[6] = 0xEC; m_rx_buf[7] = 0x00;
//			
//			memcpy(connecting_mac_addr, (const char*)&m_rx_buf + 1, 7);
//			m_rx_buf[0] = 0x52; m_rx_buf[1] = 0x81; m_rx_buf[2] = 0xFB; m_rx_buf[3] = 0xBE;
//			m_rx_buf[4] = 0x2D; m_rx_buf[5] = 0xC4; m_rx_buf[6] = 0x00; m_rx_buf[7] = 0x00;
			m_rx_buf[0] = 0xFF; m_rx_buf[1] = 0xA0; m_rx_buf[2] = 0x01; m_rx_buf[3] = 0x64;
			m_rx_buf[4] = 0x00; m_rx_buf[5] = 0x00; m_rx_buf[6] = 0x00; m_rx_buf[7] = 0x00;
			ble_nus_c_string_send(&m_ble_nus_c, m_rx_buf, 8);
		} break;

		default:
			break;
	}
}

/** @brief SPIS user event handler.
 *
 * @param event
 */
void spis_event_handler(nrf_drv_spis_event_t event)
{
	if (event.evt_type == NRF_DRV_SPIS_XFER_DONE)
	{
		spis_xfer_done = true;
		NRF_LOG_INFO(" Transfer completed");
		NRF_LOG_INFO("%02x%02x%02x%02x", m_tx_buf[0], m_tx_buf[1], m_tx_buf[2], m_tx_buf[3]);
		NRF_LOG_INFO("%02x%02x%02x%02x", m_tx_buf[4], m_tx_buf[5], m_tx_buf[6], m_tx_buf[7]);
		
		NRF_LOG_INFO(" Received");
		NRF_LOG_INFO("%02x%02x%02x%02x", m_rx_buf[0], m_rx_buf[1], m_rx_buf[2], m_rx_buf[3]);
		NRF_LOG_INFO("%02x%02x%02x%02x", m_rx_buf[4], m_rx_buf[5], m_rx_buf[6], m_rx_buf[7]);
		
		if(do_connect == false)
		{
			memcpy(connecting_mac_addr, (const char*)&m_rx_buf + 1, 7);
		}
		else if(m_rx_buf[1] == 0xA0 && do_connect == true) // Juste un choix de design que 0xA0 est la commande gerant le changement de frequence d'echantillonnage
		{
			NRF_LOG_INFO("Changing sampling frequency");
			ble_nus_c_string_send(&m_ble_nus_c, m_rx_buf, 8);
		}
	}
}


/**@brief Function for initializing the BLE stack.
 *
 * @details Initializes the SoftDevice and the BLE event interrupt.
 */
static void ble_stack_init(void)
{
	ret_code_t err_code;

	err_code = nrf_sdh_enable_request();
	APP_ERROR_CHECK(err_code);

	// Configure the BLE stack using the default settings.
	// Fetch the start address of the application RAM.
	uint32_t ram_start = 0;
	err_code = nrf_sdh_ble_default_cfg_set(APP_BLE_CONN_CFG_TAG, &ram_start);
	APP_ERROR_CHECK(err_code);

	// Enable BLE stack.
	err_code = nrf_sdh_ble_enable(&ram_start);
	APP_ERROR_CHECK(err_code);

	// Register a handler for BLE events.
	NRF_SDH_BLE_OBSERVER(m_ble_observer, APP_BLE_OBSERVER_PRIO, ble_evt_handler, NULL);
}

/**@brief Function for initializing the GATT library. */
void gatt_init(void)
{
	ret_code_t err_code;

	err_code = nrf_ble_gatt_init(&m_gatt, gatt_evt_handler);
	APP_ERROR_CHECK(err_code);

	err_code = nrf_ble_gatt_att_mtu_central_set(&m_gatt, NRF_SDH_BLE_GATT_MAX_MTU_SIZE);
	APP_ERROR_CHECK(err_code);
}

/**@brief Function for initializing the UART. */
static void uart_init(void)
{
	ret_code_t err_code;

	app_uart_comm_params_t const comm_params =
	{
		.rx_pin_no    = RX_PIN_NUMBER,
		.tx_pin_no    = TX_PIN_NUMBER,
		.rts_pin_no   = RTS_PIN_NUMBER,
		.cts_pin_no   = CTS_PIN_NUMBER,
		.flow_control = APP_UART_FLOW_CONTROL_DISABLED,
		.use_parity   = false,
		.baud_rate    = UART_BAUDRATE_BAUDRATE_Baud115200
	};

	APP_UART_FIFO_INIT(&comm_params,
			     UART_RX_BUF_SIZE,
			     UART_TX_BUF_SIZE,
			     uart_event_handle,
			     APP_IRQ_PRIORITY_LOWEST,
			     err_code);

	APP_ERROR_CHECK(err_code);
}

/**@brief Function for initializing the NUS Client. */
static void nus_c_init(void)
{
	ret_code_t       err_code;
	ble_nus_c_init_t init;

	init.evt_handler = ble_nus_c_evt_handler;

	err_code = ble_nus_c_init(&m_ble_nus_c, &init);
	APP_ERROR_CHECK(err_code);
}


/**@brief Function for initializing buttons and leds. */
static void buttons_leds_init(void)
{
	ret_code_t err_code;
	bsp_event_t startup_event;

	err_code = bsp_init(BSP_INIT_LED | BSP_INIT_BUTTONS, bsp_event_handler);
	APP_ERROR_CHECK(err_code);

	err_code = bsp_btn_ble_init(NULL, &startup_event);
	APP_ERROR_CHECK(err_code);
}


/**@brief Function for initializing the timer. */
static void timer_init(void)
{
	ret_code_t err_code = app_timer_init();
	APP_ERROR_CHECK(err_code);
}


/**@brief Function for initializing the nrf log module. */
static void log_init(void)
{
	ret_code_t err_code = NRF_LOG_INIT(NULL);
	APP_ERROR_CHECK(err_code);

	NRF_LOG_DEFAULT_BACKENDS_INIT();
}


/**@brief Function for initializing the Power manager. */
static void power_init(void)
{
	ret_code_t err_code = nrf_pwr_mgmt_init();
	APP_ERROR_CHECK(err_code);
}


/** @brief Function for initializing the Database Discovery Module. */
static void db_discovery_init(void)
{
	ret_code_t err_code = ble_db_discovery_init(db_disc_handler);
	APP_ERROR_CHECK(err_code);
}
/**@brief SPIS init function */
static void spis_init(void)
{
	// Mode par defaut = mode 0 (cpho = 0, cpha = 0)
	// ORC/DEF = 255, valeur par defaut utiliser lorsqu'il n'y a rien
	nrf_drv_spis_config_t spis_config = NRF_DRV_SPIS_DEFAULT_CONFIG;
	spis_config.csn_pin                = 29;
	spis_config.miso_pin              = 28;
	spis_config.mosi_pin              = 4;
	spis_config.sck_pin                = 3;

	APP_ERROR_CHECK(nrf_drv_spis_init(&spis, &spis_config, spis_event_handler));
}


int main(void)
{	
	// Initialisation pour pouvoir utiliser les LOGs
	log_init();
	
	// Enable the constant latency sub power mode to minimize the time it takes
	// for the SPIS peripheral to become active after the CSN line is asserted
	// (when the CPU is in sleep mode).
	NRF_POWER->TASKS_CONSTLAT = 1;
	
	// Diverses initialisations
	timer_init();
	power_init();
	uart_init();
	buttons_leds_init();
	db_discovery_init();
	ble_stack_init();
	gatt_init();
	nus_c_init();
	spis_init();

	// Start scanning for peripherals and initiate connection
	// with devices that advertise NUS UUID.
	NRF_LOG_INFO("Control Station start.");
	scan_start();

	while (1) // Main loop
	{	
		if(taille_fifo >= 32 && do_connect == false)
		{
			m_tx_buf = malloc(256);
			m_length_tx = sizeof(m_tx_buf);
			for(int i = 0; i < 31; i++)
			{
				memcpy(m_tx_buf + (i * 8), defiler(&fifo), 8);
				taille_fifo--;	
			}	
			
//			for(int i = 0; i < 255; i+=4)
//			{
//				NRF_LOG_INFO("%02x%02x%02x%02x", m_tx_buf[i], m_tx_buf[i+1], m_tx_buf[i+2], m_tx_buf[i+3]);
//			}
			taille_fifo = 0;
//			NRF_LOG_INFO("Help");
			memset(m_rx_buf, 0, m_length_rx);
			int err_code = nrf_drv_spis_buffers_set(&spis, m_tx_buf, m_length_tx, m_rx_buf, m_length_rx); // Permet de set les buffers appeler TX et RX pour une eventuelle reception SPI
			APP_ERROR_CHECK(err_code);
			spis_xfer_done = false;
		}
		
		if(spis_xfer_done == true && do_connect == true)
		{	
			if(taille_fifo > 0)
			{
				m_tx_buf = malloc(256);
				m_length_tx = sizeof(m_tx_buf);
				sd_nvic_critical_region_enter(&is_nested);
				for(int i = 0; i < 31; i++)
				{
					memcpy(m_tx_buf + (i * 8), defiler(&fifo), 8);
					taille_fifo--;
				}
				sd_nvic_critical_region_exit(is_nested);
				
//				NRF_LOG_INFO("Took in FIFO");
//				NRF_LOG_INFO("%s", m_tx_buf);
				
				memset(m_rx_buf, 0, m_length_rx);
				int err_code = nrf_drv_spis_buffers_set(&spis, m_tx_buf, m_length_tx, m_rx_buf, m_length_rx); // Permet de set les buffers appeler TX et RX pour une eventuelle reception SPI
				APP_ERROR_CHECK(err_code);
				spis_xfer_done = false;
			}
		}
		
		if (NRF_LOG_PROCESS() == false)
		{
			nrf_pwr_mgmt_run(); // Fonction de power management (low energy)
			NRF_LOG_FLUSH();
		}
	}
}
